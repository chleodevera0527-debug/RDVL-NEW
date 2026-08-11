import os
import sys
import csv
import io
import json
import hmac
import hashlib
import secrets
import sqlite3
import threading
import time
import re
from contextlib import closing
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo
from html import escape
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlencode, urlparse

try:
    import psycopg2
    from psycopg2 import IntegrityError as PostgresIntegrityError
    from psycopg2.extras import RealDictCursor
except ImportError:
    psycopg2 = None
    PostgresIntegrityError = Exception
    RealDictCursor = None

if getattr(sys, "frozen", False):
    ROOT = Path(sys.executable).resolve().parent
else:
    ROOT = Path(__file__).resolve().parent

DATABASE_URL = os.getenv("DATABASE_URL", "").strip()
USE_POSTGRES = bool(DATABASE_URL)
DB = ROOT / os.getenv("TRUCK_DB", "truck_monitor.db")
PORT = int(os.getenv("PORT", "8090"))
LIVE_REFRESH_SECONDS = 5
MAX_REQUEST_BYTES = 1_000_000
SCHEMA_VERSION = 6
SESSION_DAYS = 7
LOGIN_WINDOW_SECONDS = 300
LOGIN_MAX_FAILURES = 8
_INIT_LOCK = threading.RLock()
_INITIALIZED = False
_LOGIN_FAILURES = {}
COOKIE_SECURE = os.getenv("COOKIE_SECURE", "0") == "1"
APP_SECRET = os.getenv("APP_SECRET", "").strip()

DBIntegrityError = PostgresIntegrityError if USE_POSTGRES and psycopg2 else sqlite3.IntegrityError

TIMES = [
    ("port_arrival", "Arrival at port"),
    ("port_departure", "Departure from port"),
    ("delivery_arrival", "Arrival at delivery site"),
    ("unloading_start", "Start unloading"),
    ("unloading_finish", "Finish unloading"),
    ("delivery_departure", "Departure from delivery site"),
    ("yard_dropped", "Dropped in court yard"),
    ("yard_pullout", "Yard pullout"),
    ("returned_port", "Returned to port"),
]
TIME_KEYS = [k for k, _ in TIMES]
TIME_LABELS = dict(TIMES)
STATUSES = ["Dispatched", "At Port", "In Transit", "At Delivery Site", "Unloading", "In Court Yard", "Returned to Port", "Completed", "On Hold"]
PRIORITIES = ["Normal", "High", "Urgent"]
ROLES = ["Admin", "Dispatcher", "Driver", "Viewer"]
CARGO_TYPES = ["", "Containarized (20)", "Containarized (40)", "Loose Cargo", "Low Bed", "ISO Tank"]
SHIPPING_LINES = [
    "Maersk", "MSC – Mediterranean Shipping Company", "CMA CGM", "COSCO", "Evergreen Line",
    "Hapag-Lloyd", "Ocean Network Express (ONE)", "OOCL", "PIL – Pacific International Lines",
    "Yang Ming", "Wan Hai Lines", "KMTC", "SITC Container Lines", "TS Lines", "RCL",
    "Hyundai Merchant Marine / HMM", "K Line", "Sinokor", "Pan Ocean", "Unifeeder",
    "Heung-A Line", "Namsung Shipping", "Emirates Shipping Line", "Sealead Shipping",
    "Sinotrans", "New Golden Sea Shipping"
]

class DBConnection:
    def __init__(self, connection):
        self.connection = connection
    def _sql(self, sql):
        if USE_POSTGRES:
            sql = sql.replace("BEGIN", "BEGIN")
            return re.sub(r"(?<!%)\?", "%s", sql)
        return sql
    def execute(self, sql, params=()):
        if USE_POSTGRES:
            cur = self.connection.cursor(cursor_factory=RealDictCursor)
            cur.execute(self._sql(sql), params)
            return cur
        return self.connection.execute(sql, params)
    def executemany(self, sql, seq):
        if USE_POSTGRES:
            cur = self.connection.cursor(cursor_factory=RealDictCursor)
            cur.executemany(self._sql(sql), seq)
            return cur
        return self.connection.executemany(sql, seq)
    def executescript(self, sql):
        if USE_POSTGRES:
            with self.connection.cursor() as cur:
                cur.execute(sql)
                return cur
        return self.connection.executescript(sql)
    def commit(self):
        self.connection.commit()
    def rollback(self):
        self.connection.rollback()
    def close(self):
        self.connection.close()
    def __enter__(self):
        return self
    def __exit__(self, exc_type, exc_value, traceback):
        if exc_type:
            self.rollback()
        self.close()
    @property
    def total_changes(self):
        if USE_POSTGRES:
            return 0
        return self.connection.total_changes

APP_TIMEZONE = os.getenv("TIMEZONE", "Asia/Manila").strip() or "Asia/Manila"
try:
    APP_TZ = ZoneInfo(APP_TIMEZONE)
except Exception:
    APP_TIMEZONE = "Asia/Manila"
    APP_TZ = ZoneInfo(APP_TIMEZONE)

def ph_now():
    return datetime.now(APP_TZ).replace(tzinfo=None)

def now_iso():
    return ph_now().isoformat(timespec="seconds")

def parse_dt(value):
    if not value:
        return None
    try:
        dt = datetime.fromisoformat(str(value).replace("Z", "+00:00"))
        if dt.tzinfo is not None:
            dt = dt.astimezone(APP_TZ).replace(tzinfo=None)
        return dt
    except (TypeError, ValueError):
        return None

def db():
    if USE_POSTGRES:
        if psycopg2 is None:
            raise RuntimeError("PostgreSQL support requires psycopg2-binary.")
        return DBConnection(psycopg2.connect(DATABASE_URL, connect_timeout=10))
    con = sqlite3.connect(DB, timeout=15)
    con.row_factory = sqlite3.Row
    con.execute("PRAGMA foreign_keys = ON")
    con.execute("PRAGMA busy_timeout = 15000")
    con.execute("PRAGMA journal_mode = WAL")
    con.execute("PRAGMA synchronous = FULL")
    return DBConnection(con)


def sql_values(values):
    return ", ".join("'" + v.replace("'", "''") + "'" for v in values)


def effective_status(d):
                                                                           
                                                                      
    if d.get("status") == "On Hold":
        return "On Hold"
    if d.get("returned_port"):
        return "Returned to Port"
    if d.get("yard_pullout"):
        return "In Transit"
    if d.get("yard_dropped"):
        return "In Court Yard"
    if d.get("delivery_departure"):
        return "Completed"
    if d.get("unloading_start") and not d.get("unloading_finish"):
        return "Unloading"
    if d.get("unloading_finish"):
        return "At Delivery Site"
    if d.get("delivery_arrival"):
        return "At Delivery Site"
    if d.get("port_departure"):
        return "In Transit"
    if d.get("port_arrival"):
        return "At Port"
    return "Dispatched"


def status_case_sql(prefix="NEW."):
    return f"""CASE
        WHEN COALESCE({prefix}returned_port, '') <> '' THEN 'Returned to Port'
        WHEN COALESCE({prefix}yard_pullout, '') <> '' THEN 'In Transit'
        WHEN COALESCE({prefix}yard_dropped, '') <> '' THEN 'In Court Yard'
        WHEN COALESCE({prefix}delivery_departure, '') <> '' THEN 'Completed'
        WHEN COALESCE({prefix}unloading_start, '') <> '' AND COALESCE({prefix}unloading_finish, '') = '' THEN 'Unloading'
        WHEN COALESCE({prefix}unloading_finish, '') <> '' THEN 'At Delivery Site'
        WHEN COALESCE({prefix}delivery_arrival, '') <> '' THEN 'At Delivery Site'
        WHEN COALESCE({prefix}port_departure, '') <> '' THEN 'In Transit'
        WHEN COALESCE({prefix}port_arrival, '') <> '' THEN 'At Port'
        ELSE 'Dispatched'
    END"""


def install_database_guards(con):
    checks = [
        ("TRIM(COALESCE(NEW.container_no,''))=''", "Container number is required."),
        ("TRIM(COALESCE(NEW.driver_name,''))=''", "Driver name is required."),
        ("TRIM(COALESCE(NEW.contact_no,''))=''", "Contact number is required."),
        (f"COALESCE(NEW.status,'') NOT IN ({sql_values(STATUSES)})", "Invalid status."),
        (f"COALESCE(NEW.priority,'') NOT IN ({sql_values(PRIORITIES)})", "Invalid priority."),
        ("NEW.created_at IS NULL OR datetime(NEW.created_at) IS NULL", "Invalid created timestamp."),
        ("NEW.updated_at IS NULL OR datetime(NEW.updated_at) IS NULL", "Invalid updated timestamp."),
    ]
    for key, label in TIMES:
        checks.append((f"COALESCE(NEW.{key},'')<>'' AND datetime(NEW.{key}) IS NULL", f"{label}: invalid date/time."))
    checks += [
        ("COALESCE(NEW.latitude,'')<>'' AND (NEW.latitude < -90 OR NEW.latitude > 90)", "Latitude must be between -90 and 90."),
        ("COALESCE(NEW.longitude,'')<>'' AND (NEW.longitude < -180 OR NEW.longitude > 180)", "Longitude must be between -180 and 180."),
    ]
    deps = [
        ("port_departure", "port_arrival", "Port departure requires port arrival."),
        ("delivery_arrival", "port_departure", "Delivery arrival requires port departure."),
        ("unloading_start", "delivery_arrival", "Unloading start requires delivery arrival."),
        ("unloading_finish", "unloading_start", "Unloading finish requires unloading start."),
        ("delivery_departure", "unloading_finish", "Delivery departure requires unloading finish."),
        ("yard_dropped", "delivery_departure", "Yard dropped requires delivery departure."),
        ("yard_pullout", "yard_dropped", "Yard pullout requires a prior yard dropped event."),
        ("returned_port", "delivery_departure", "Returned to port requires delivery departure."),
    ]
    for later, earlier, msg in deps:
        checks.append((f"COALESCE(NEW.{later},'')<>'' AND (COALESCE(NEW.{earlier},'')='' OR NEW.{later}<NEW.{earlier})", msg))
    checks.append(("COALESCE(NEW.returned_port,'')<>'' AND COALESCE(NEW.yard_dropped,'')<>'' AND (COALESCE(NEW.yard_pullout,'')='' OR NEW.returned_port<NEW.yard_pullout)", "Returned to port requires a prior yard pullout when the container was dropped in the yard."))

    validation = []
    for condition, message in checks:
        validation.append(f"SELECT CASE WHEN {condition} THEN RAISE(ABORT, '{message.replace(chr(39), chr(39)*2)}') END;")
    validation_sql = "\n".join(validation)
    computed = status_case_sql()

    for name in ("trips_validate_insert", "trips_validate_update", "trips_sync_status_insert", "trips_sync_status_update", "trips_milestones_immutable", "trips_touch_updated_at"):
        con.execute(f"DROP TRIGGER IF EXISTS {name}")

    con.executescript(f"""
    CREATE TRIGGER trips_validate_insert BEFORE INSERT ON trips BEGIN
        {validation_sql}
    END;
    CREATE TRIGGER trips_validate_update BEFORE UPDATE ON trips BEGIN
        {validation_sql}
    END;
    CREATE TRIGGER trips_sync_status_insert AFTER INSERT ON trips
    WHEN NEW.status <> 'On Hold' AND NEW.status <> ({computed}) BEGIN
        UPDATE trips SET status=({computed}) WHERE id=NEW.id;
    END;
    CREATE TRIGGER trips_sync_status_update AFTER UPDATE ON trips
    WHEN NEW.status <> 'On Hold' AND NEW.status <> ({computed}) BEGIN
        UPDATE trips SET status=({computed}) WHERE id=NEW.id;
    END;
    CREATE TRIGGER trips_milestones_immutable BEFORE UPDATE ON trips BEGIN
        SELECT CASE WHEN COALESCE(OLD.port_arrival,'')<>'' AND NEW.port_arrival<>OLD.port_arrival THEN RAISE(ABORT,'Arrival at port is immutable once recorded.') END;
        SELECT CASE WHEN COALESCE(OLD.port_departure,'')<>'' AND NEW.port_departure<>OLD.port_departure THEN RAISE(ABORT,'Departure from port is immutable once recorded.') END;
        SELECT CASE WHEN COALESCE(OLD.delivery_arrival,'')<>'' AND NEW.delivery_arrival<>OLD.delivery_arrival THEN RAISE(ABORT,'Arrival at delivery site is immutable once recorded.') END;
        SELECT CASE WHEN COALESCE(OLD.unloading_start,'')<>'' AND NEW.unloading_start<>OLD.unloading_start THEN RAISE(ABORT,'Start unloading is immutable once recorded.') END;
        SELECT CASE WHEN COALESCE(OLD.unloading_finish,'')<>'' AND NEW.unloading_finish<>OLD.unloading_finish THEN RAISE(ABORT,'Finish unloading is immutable once recorded.') END;
        SELECT CASE WHEN COALESCE(OLD.delivery_departure,'')<>'' AND NEW.delivery_departure<>OLD.delivery_departure THEN RAISE(ABORT,'Departure from delivery site is immutable once recorded.') END;
        SELECT CASE WHEN COALESCE(OLD.yard_dropped,'')<>'' AND NEW.yard_dropped<>OLD.yard_dropped THEN RAISE(ABORT,'Yard dropped is immutable once recorded.') END;
        SELECT CASE WHEN COALESCE(OLD.yard_pullout,'')<>'' AND NEW.yard_pullout<>OLD.yard_pullout THEN RAISE(ABORT,'Yard pullout is immutable once recorded.') END;
        SELECT CASE WHEN COALESCE(OLD.returned_port,'')<>'' AND NEW.returned_port<>OLD.returned_port THEN RAISE(ABORT,'Returned to port is immutable once recorded.') END;
    END;
    CREATE TRIGGER trips_touch_updated_at
    AFTER UPDATE OF container_no,driver_name,contact_no,status,priority,current_location,court_yard_name,
      cargo_type,shipping_line,client,latitude,longitude,last_location_at,assigned_user,port_arrival,port_departure,
      delivery_arrival,unloading_start,unloading_finish,delivery_departure,yard_dropped,yard_pullout,
      returned_port,tags,notes,updated_by ON trips
    WHEN NEW.updated_at=OLD.updated_at BEGIN
      UPDATE trips SET updated_at=strftime('%Y-%m-%dT%H:%M:%S','now','localtime') WHERE id=NEW.id;
    END;
    """)

    indexes = [
        "CREATE INDEX IF NOT EXISTS idx_trips_updated_at_id ON trips(updated_at DESC,id DESC)",
        "CREATE INDEX IF NOT EXISTS idx_trips_status ON trips(status)",
        "CREATE INDEX IF NOT EXISTS idx_trips_priority ON trips(priority)",
        "CREATE INDEX IF NOT EXISTS idx_trips_driver ON trips(driver_name)",
        "CREATE INDEX IF NOT EXISTS idx_trips_client ON trips(client)",
        "CREATE INDEX IF NOT EXISTS idx_trips_location ON trips(latitude,longitude)",
        "CREATE INDEX IF NOT EXISTS idx_trips_assigned_user ON trips(assigned_user)",
        "CREATE INDEX IF NOT EXISTS idx_trips_created_by ON trips(created_by)",
        "CREATE INDEX IF NOT EXISTS idx_trips_updated_by ON trips(updated_by)",
        "CREATE INDEX IF NOT EXISTS idx_trips_client_updated ON trips(client,updated_at DESC)",
    ]
    for sql in indexes:
        con.execute(sql)


def _initialize_sqlite_database():
    with closing(db()) as con:
        con.execute("""CREATE TABLE IF NOT EXISTS trips (
            id INTEGER PRIMARY KEY,
            container_no TEXT NOT NULL UNIQUE,
            driver_name TEXT NOT NULL,
            contact_no TEXT NOT NULL,
            status TEXT NOT NULL DEFAULT 'Dispatched',
            priority TEXT NOT NULL DEFAULT 'Normal',
            current_location TEXT,
            court_yard_name TEXT,
            cargo_type TEXT,
            shipping_line TEXT,
            client TEXT,
            port_arrival TEXT, port_departure TEXT, delivery_arrival TEXT,
            unloading_start TEXT, unloading_finish TEXT, delivery_departure TEXT,
            yard_dropped TEXT, yard_pullout TEXT, returned_port TEXT,
            tags TEXT, notes TEXT, created_at TEXT NOT NULL, updated_at TEXT NOT NULL,
            latitude REAL, longitude REAL, last_location_at TEXT,
            assigned_user TEXT, created_by TEXT, updated_by TEXT
        )""")
        con.execute("""CREATE TABLE IF NOT EXISTS activity_log (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            trip_id INTEGER,
            username TEXT,
            action TEXT NOT NULL,
            details TEXT,
            created_at TEXT NOT NULL,
            FOREIGN KEY(trip_id) REFERENCES trips(id) ON DELETE CASCADE
        )""")
        con.execute("""CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT NOT NULL UNIQUE,
            password_hash TEXT NOT NULL,
            role TEXT NOT NULL,
            driver_name TEXT,
            client_name TEXT,
            active INTEGER NOT NULL DEFAULT 1,
            created_at TEXT NOT NULL
        )""")
        con.execute("""CREATE TABLE IF NOT EXISTS truckers (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL UNIQUE COLLATE NOCASE,
            active INTEGER NOT NULL DEFAULT 1,
            created_at TEXT NOT NULL,
            created_by TEXT
        )""")
        con.execute("""CREATE TABLE IF NOT EXISTS clients (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL UNIQUE COLLATE NOCASE,
            active INTEGER NOT NULL DEFAULT 1,
            created_at TEXT NOT NULL,
            created_by TEXT
        )""")
        con.execute("""CREATE TABLE IF NOT EXISTS sessions (
            token_hash TEXT PRIMARY KEY,
            username TEXT NOT NULL,
            expires_at TEXT NOT NULL,
            created_at TEXT NOT NULL
        )""")
        con.execute("""CREATE TABLE IF NOT EXISTS app_events (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            level TEXT NOT NULL,
            message TEXT NOT NULL,
            trip_id INTEGER,
            created_at TEXT NOT NULL,
            resolved INTEGER NOT NULL DEFAULT 0,
            FOREIGN KEY(trip_id) REFERENCES trips(id) ON DELETE CASCADE
        )""")

        existing = {r["name"] for r in con.execute("PRAGMA table_info(trips)")}
        additions = {
            "yard_pullout": "TEXT", "trucker_name": "TEXT", "priority": "TEXT DEFAULT 'Normal'",
            "court_yard_name": "TEXT", "shipping_line": "TEXT", "latitude": "REAL", "longitude": "REAL",
            "last_location_at": "TEXT", "assigned_user": "TEXT", "created_by": "TEXT", "updated_by": "TEXT",
        }
        for name, definition in additions.items():
            if name not in existing:
                con.execute(f"ALTER TABLE trips ADD COLUMN {name} {definition}")

        activity_cols = {r["name"] for r in con.execute("PRAGMA table_info(activity_log)")}
        if "username" not in activity_cols:
            con.execute("ALTER TABLE activity_log ADD COLUMN username TEXT")
        user_cols = {r["name"] for r in con.execute("PRAGMA table_info(users)")}
        if "client_name" not in user_cols:
            con.execute("ALTER TABLE users ADD COLUMN client_name TEXT")

        con.execute("UPDATE trips SET priority='Normal' WHERE priority IS NULL OR priority=''")
                                                                                       
        for row in con.execute("SELECT * FROM trips").fetchall():
            expected = effective_status(dict(row))
            if row["status"] != expected:
                con.execute("UPDATE trips SET status=? WHERE id=?", (expected, row["id"]))

        con.execute("CREATE INDEX IF NOT EXISTS idx_activity_trip_created ON activity_log(trip_id,created_at DESC)")
        con.execute("CREATE INDEX IF NOT EXISTS idx_activity_created ON activity_log(created_at DESC)")
        con.execute("CREATE INDEX IF NOT EXISTS idx_users_username ON users(username)")
        con.execute("CREATE INDEX IF NOT EXISTS idx_sessions_expiry ON sessions(expires_at)")
        con.execute("CREATE INDEX IF NOT EXISTS idx_truckers_name ON truckers(name)")
        con.execute("CREATE INDEX IF NOT EXISTS idx_clients_name ON clients(name)")
        con.execute("""INSERT OR IGNORE INTO truckers(name,created_at,created_by)
                       SELECT TRIM(trucker_name), ?, 'migration'
                       FROM trips WHERE TRIM(COALESCE(trucker_name,''))<>''""", (now_iso(),))
        con.execute("""INSERT OR IGNORE INTO clients(name,created_at,created_by)
                       SELECT TRIM(client), ?, 'migration'
                       FROM trips WHERE TRIM(COALESCE(client,''))<>''""", (now_iso(),))
        con.execute("CREATE INDEX IF NOT EXISTS idx_events_open ON app_events(resolved,created_at DESC)")
        install_database_guards(con)
        con.execute(f"PRAGMA user_version = {SCHEMA_VERSION}")

                                                                                                           
        admin_user = os.getenv("ADMIN_USERNAME", "admin").strip() or "admin"
        allow_default = os.getenv("ALLOW_DEFAULT_ADMIN", "0") == "1"
        admin_password = os.getenv("ADMIN_PASSWORD", "").strip()
        reset_admin = os.getenv("ADMIN_PASSWORD_RESET", "0") == "1"
        if not admin_password and allow_default:
            admin_password = "Admin@12345"
        if admin_password:
            existing_admin = con.execute("SELECT id FROM users WHERE username=?", (admin_user,)).fetchone()
            if not existing_admin:
                con.execute("INSERT INTO users(username,password_hash,role,created_at) VALUES(?,?,?,?)", (admin_user, hash_password(admin_password), "Admin", now_iso()))
            elif reset_admin:
                con.execute("UPDATE users SET password_hash=?, role='Admin', active=1 WHERE username=?", (hash_password(admin_password), admin_user))
        con.commit()


def _initialize_postgres_database():
    if psycopg2 is None:
        raise RuntimeError("psycopg2-binary is required when DATABASE_URL is set.")
    with closing(db()) as con:
        con.execute("SELECT pg_advisory_lock(814726510)")
        con.execute("""CREATE TABLE IF NOT EXISTS trips (
            id BIGSERIAL PRIMARY KEY, container_no TEXT NOT NULL UNIQUE, driver_name TEXT NOT NULL, contact_no TEXT NOT NULL,
            status TEXT NOT NULL DEFAULT 'Dispatched', priority TEXT NOT NULL DEFAULT 'Normal', current_location TEXT,
            court_yard_name TEXT, cargo_type TEXT, shipping_line TEXT, client TEXT, port_arrival TEXT, port_departure TEXT,
            delivery_arrival TEXT, unloading_start TEXT, unloading_finish TEXT, delivery_departure TEXT, yard_dropped TEXT,
            yard_pullout TEXT, returned_port TEXT, tags TEXT, notes TEXT, created_at TEXT NOT NULL, updated_at TEXT NOT NULL,
            latitude DOUBLE PRECISION, longitude DOUBLE PRECISION, last_location_at TEXT, assigned_user TEXT, created_by TEXT, updated_by TEXT
        )""")
        con.execute("""CREATE TABLE IF NOT EXISTS activity_log (
            id BIGSERIAL PRIMARY KEY, trip_id BIGINT REFERENCES trips(id) ON DELETE CASCADE, username TEXT, action TEXT NOT NULL, details TEXT, created_at TEXT NOT NULL
        )""")
        con.execute("""CREATE TABLE IF NOT EXISTS users (
            id BIGSERIAL PRIMARY KEY, username TEXT NOT NULL UNIQUE, password_hash TEXT NOT NULL, role TEXT NOT NULL, driver_name TEXT, client_name TEXT, active INTEGER NOT NULL DEFAULT 1, created_at TEXT NOT NULL
        )""")
        con.execute("""CREATE TABLE IF NOT EXISTS truckers (
            id BIGSERIAL PRIMARY KEY, name TEXT NOT NULL, active INTEGER NOT NULL DEFAULT 1, created_at TEXT NOT NULL, created_by TEXT
        )""")
        con.execute("""CREATE TABLE IF NOT EXISTS clients (
            id BIGSERIAL PRIMARY KEY, name TEXT NOT NULL, active INTEGER NOT NULL DEFAULT 1, created_at TEXT NOT NULL, created_by TEXT
        )""")
        con.execute("""CREATE TABLE IF NOT EXISTS sessions (
            token_hash TEXT PRIMARY KEY, username TEXT NOT NULL, expires_at TEXT NOT NULL, created_at TEXT NOT NULL
        )""")
        con.execute("""CREATE TABLE IF NOT EXISTS app_events (
            id BIGSERIAL PRIMARY KEY, level TEXT NOT NULL, message TEXT NOT NULL, trip_id BIGINT REFERENCES trips(id) ON DELETE CASCADE, created_at TEXT NOT NULL, resolved INTEGER NOT NULL DEFAULT 0
        )""")
        additions = {
            "yard_pullout":"TEXT", "trucker_name":"TEXT", "priority":"TEXT DEFAULT 'Normal'", "court_yard_name":"TEXT",
            "shipping_line":"TEXT", "latitude":"DOUBLE PRECISION", "longitude":"DOUBLE PRECISION", "last_location_at":"TEXT",
            "assigned_user":"TEXT", "created_by":"TEXT", "updated_by":"TEXT"
        }
        for name, definition in additions.items():
            con.execute(f"ALTER TABLE trips ADD COLUMN IF NOT EXISTS {name} {definition}")
        con.execute("ALTER TABLE activity_log ADD COLUMN IF NOT EXISTS username TEXT")
        con.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS client_name TEXT")
        con.execute("UPDATE trips SET priority='Normal' WHERE priority IS NULL OR priority=''")
        con.execute("CREATE UNIQUE INDEX IF NOT EXISTS ux_truckers_name_ci ON truckers (LOWER(name))")
        con.execute("CREATE UNIQUE INDEX IF NOT EXISTS ux_clients_name_ci ON clients (LOWER(name))")
        indexes = [
            "CREATE INDEX IF NOT EXISTS idx_trips_updated_at_id ON trips(updated_at DESC,id DESC)",
            "CREATE INDEX IF NOT EXISTS idx_trips_status ON trips(status)",
            "CREATE INDEX IF NOT EXISTS idx_trips_priority ON trips(priority)",
            "CREATE INDEX IF NOT EXISTS idx_trips_driver ON trips(driver_name)",
            "CREATE INDEX IF NOT EXISTS idx_trips_client ON trips(client)",
            "CREATE INDEX IF NOT EXISTS idx_trips_location ON trips(latitude,longitude)",
            "CREATE INDEX IF NOT EXISTS idx_trips_assigned_user ON trips(assigned_user)",
            "CREATE INDEX IF NOT EXISTS idx_trips_created_by ON trips(created_by)",
            "CREATE INDEX IF NOT EXISTS idx_trips_updated_by ON trips(updated_by)",
            "CREATE INDEX IF NOT EXISTS idx_trips_client_updated ON trips(client,updated_at DESC)",
            "CREATE INDEX IF NOT EXISTS idx_activity_trip_created ON activity_log(trip_id,created_at DESC)",
            "CREATE INDEX IF NOT EXISTS idx_activity_created ON activity_log(created_at DESC)",
            "CREATE INDEX IF NOT EXISTS idx_users_username ON users(username)",
            "CREATE INDEX IF NOT EXISTS idx_sessions_expiry ON sessions(expires_at)",
            "CREATE INDEX IF NOT EXISTS idx_truckers_name ON truckers(name)",
            "CREATE INDEX IF NOT EXISTS idx_clients_name ON clients(name)",
            "CREATE INDEX IF NOT EXISTS idx_events_open ON app_events(resolved,created_at DESC)"
        ]
        for sql in indexes:
            con.execute(sql)
        con.execute("""CREATE OR REPLACE FUNCTION rdevera_trips_guard() RETURNS trigger AS $$
DECLARE
    status_expected TEXT;
BEGIN
    IF BTRIM(COALESCE(NEW.container_no,''))='' THEN RAISE EXCEPTION 'Container number is required.' USING ERRCODE='23514'; END IF;
    IF BTRIM(COALESCE(NEW.driver_name,''))='' THEN RAISE EXCEPTION 'Driver name is required.' USING ERRCODE='23514'; END IF;
    IF BTRIM(COALESCE(NEW.contact_no,''))='' THEN RAISE EXCEPTION 'Contact number is required.' USING ERRCODE='23514'; END IF;
    IF COALESCE(NEW.priority,'') NOT IN ('Normal','High','Urgent') THEN RAISE EXCEPTION 'Invalid priority.' USING ERRCODE='23514'; END IF;
    IF NEW.port_departure<>'' AND (COALESCE(NEW.port_arrival,'')='' OR NEW.port_departure<NEW.port_arrival) THEN RAISE EXCEPTION 'Port departure requires port arrival.' USING ERRCODE='23514'; END IF;
    IF NEW.delivery_arrival<>'' AND (COALESCE(NEW.port_departure,'')='' OR NEW.delivery_arrival<NEW.port_departure) THEN RAISE EXCEPTION 'Delivery arrival requires port departure.' USING ERRCODE='23514'; END IF;
    IF NEW.unloading_start<>'' AND (COALESCE(NEW.delivery_arrival,'')='' OR NEW.unloading_start<NEW.delivery_arrival) THEN RAISE EXCEPTION 'Unloading start requires delivery arrival.' USING ERRCODE='23514'; END IF;
    IF NEW.unloading_finish<>'' AND (COALESCE(NEW.unloading_start,'')='' OR NEW.unloading_finish<NEW.unloading_start) THEN RAISE EXCEPTION 'Unloading finish requires unloading start.' USING ERRCODE='23514'; END IF;
    IF NEW.delivery_departure<>'' AND (COALESCE(NEW.unloading_finish,'')='' OR NEW.delivery_departure<NEW.unloading_finish) THEN RAISE EXCEPTION 'Delivery departure requires unloading finish.' USING ERRCODE='23514'; END IF;
    IF NEW.yard_dropped<>'' AND (COALESCE(NEW.delivery_departure,'')='' OR NEW.yard_dropped<NEW.delivery_departure) THEN RAISE EXCEPTION 'Yard dropped requires delivery departure.' USING ERRCODE='23514'; END IF;
    IF NEW.yard_pullout<>'' AND (COALESCE(NEW.yard_dropped,'')='' OR NEW.yard_pullout<NEW.yard_dropped) THEN RAISE EXCEPTION 'Yard pullout requires a prior yard dropped event.' USING ERRCODE='23514'; END IF;
    IF NEW.returned_port<>'' AND COALESCE(NEW.delivery_departure,'')='' THEN RAISE EXCEPTION 'Returned to port requires delivery departure.' USING ERRCODE='23514'; END IF;
    IF NEW.returned_port<>'' AND COALESCE(NEW.yard_dropped,'')<>'' AND (COALESCE(NEW.yard_pullout,'')='' OR NEW.returned_port<NEW.yard_pullout) THEN RAISE EXCEPTION 'Returned to port requires a prior yard pullout when the container was dropped in the yard.' USING ERRCODE='23514'; END IF;
    IF TG_OP='UPDATE' THEN
        IF COALESCE(OLD.port_arrival,'')<>'' AND NEW.port_arrival<>OLD.port_arrival THEN RAISE EXCEPTION 'Arrival at port is immutable once recorded.' USING ERRCODE='23514'; END IF;
        IF COALESCE(OLD.port_departure,'')<>'' AND NEW.port_departure<>OLD.port_departure THEN RAISE EXCEPTION 'Departure from port is immutable once recorded.' USING ERRCODE='23514'; END IF;
        IF COALESCE(OLD.delivery_arrival,'')<>'' AND NEW.delivery_arrival<>OLD.delivery_arrival THEN RAISE EXCEPTION 'Arrival at delivery site is immutable once recorded.' USING ERRCODE='23514'; END IF;
        IF COALESCE(OLD.unloading_start,'')<>'' AND NEW.unloading_start<>OLD.unloading_start THEN RAISE EXCEPTION 'Start unloading is immutable once recorded.' USING ERRCODE='23514'; END IF;
        IF COALESCE(OLD.unloading_finish,'')<>'' AND NEW.unloading_finish<>OLD.unloading_finish THEN RAISE EXCEPTION 'Finish unloading is immutable once recorded.' USING ERRCODE='23514'; END IF;
        IF COALESCE(OLD.delivery_departure,'')<>'' AND NEW.delivery_departure<>OLD.delivery_departure THEN RAISE EXCEPTION 'Departure from delivery site is immutable once recorded.' USING ERRCODE='23514'; END IF;
        IF COALESCE(OLD.yard_dropped,'')<>'' AND NEW.yard_dropped<>OLD.yard_dropped THEN RAISE EXCEPTION 'Yard dropped is immutable once recorded.' USING ERRCODE='23514'; END IF;
        IF COALESCE(OLD.yard_pullout,'')<>'' AND NEW.yard_pullout<>OLD.yard_pullout THEN RAISE EXCEPTION 'Yard pullout is immutable once recorded.' USING ERRCODE='23514'; END IF;
        IF COALESCE(OLD.returned_port,'')<>'' AND NEW.returned_port<>OLD.returned_port THEN RAISE EXCEPTION 'Returned to port is immutable once recorded.' USING ERRCODE='23514'; END IF;
    END IF;
    IF COALESCE(NEW.status,'') <> 'On Hold' THEN
        status_expected := CASE
            WHEN COALESCE(NEW.returned_port,'')<>'' THEN 'Returned to Port'
            WHEN COALESCE(NEW.yard_pullout,'')<>'' THEN 'In Transit'
            WHEN COALESCE(NEW.yard_dropped,'')<>'' THEN 'In Court Yard'
            WHEN COALESCE(NEW.delivery_departure,'')<>'' THEN 'Completed'
            WHEN COALESCE(NEW.unloading_start,'')<>'' AND COALESCE(NEW.unloading_finish,'')='' THEN 'Unloading'
            WHEN COALESCE(NEW.unloading_finish,'')<>'' THEN 'At Delivery Site'
            WHEN COALESCE(NEW.delivery_arrival,'')<>'' THEN 'At Delivery Site'
            WHEN COALESCE(NEW.port_departure,'')<>'' THEN 'In Transit'
            WHEN COALESCE(NEW.port_arrival,'')<>'' THEN 'At Port'
            ELSE 'Dispatched' END;
        NEW.status := status_expected;
    END IF;
    NEW.updated_at := COALESCE(NULLIF(NEW.updated_at,''), to_char(clock_timestamp(),'YYYY-MM-DD"T"HH24:MI:SS'));
    RETURN NEW;
END;
$$ LANGUAGE plpgsql;""")
        con.execute("DROP TRIGGER IF EXISTS trips_guard ON trips")
        con.execute("CREATE TRIGGER trips_guard BEFORE INSERT OR UPDATE ON trips FOR EACH ROW EXECUTE FUNCTION rdevera_trips_guard()")
        for row in con.execute("SELECT * FROM trips").fetchall():
            expected=effective_status(dict(row))
            if row["status"]!=expected:
                con.execute("UPDATE trips SET status=? WHERE id=?",(expected,row["id"]))
        admin_user=os.getenv("ADMIN_USERNAME","admin").strip() or "admin"
        admin_password=os.getenv("ADMIN_PASSWORD","").strip()
        allow_default=os.getenv("ALLOW_DEFAULT_ADMIN","0")=="1"
        reset_admin=os.getenv("ADMIN_PASSWORD_RESET","0")=="1"
        if not admin_password and allow_default:
            admin_password="Admin@12345"
        if admin_password:
            row=con.execute("SELECT id FROM users WHERE username=?",(admin_user,)).fetchone()
            if not row:
                con.execute("INSERT INTO users(username,password_hash,role,created_at) VALUES(?,?,?,?)",(admin_user,hash_password(admin_password),"Admin",now_iso()))
            elif reset_admin:
                con.execute("UPDATE users SET password_hash=?,role='Admin',active=1 WHERE username=?",(hash_password(admin_password),admin_user))
        con.commit()
        con.execute("SELECT pg_advisory_unlock(814726510)")

def _initialize_database():
    if USE_POSTGRES:
        _initialize_postgres_database()
    else:
        _initialize_sqlite_database()

def initialize():
    global _INITIALIZED
    if _INITIALIZED:
        return
    with _INIT_LOCK:
        if _INITIALIZED:
            return
        _initialize_database()
        _INITIALIZED=True


def hash_password(password, salt=None):
    salt = salt or secrets.token_bytes(16)
    digest = hashlib.pbkdf2_hmac("sha256", password.encode(), salt, 210_000)
    return "pbkdf2_sha256$210000$" + salt.hex() + "$" + digest.hex()


def verify_password(password, encoded):
    try:
        scheme, rounds, salt_hex, digest_hex = encoded.split("$")
        if scheme != "pbkdf2_sha256":
            return False
        candidate = hashlib.pbkdf2_hmac("sha256", password.encode(), bytes.fromhex(salt_hex), int(rounds)).hex()
        return hmac.compare_digest(candidate, digest_hex)
    except Exception:
        return False


def login_allowed(username):
    now = time.time()
    item = _LOGIN_FAILURES.get(username)
    if not item:
        return True
    start, count = item
    if now - start >= LOGIN_WINDOW_SECONDS:
        _LOGIN_FAILURES.pop(username, None)
        return True
    return count < LOGIN_MAX_FAILURES


def note_login_failure(username):
    now = time.time()
    start, count = _LOGIN_FAILURES.get(username, (now, 0))
    if now - start >= LOGIN_WINDOW_SECONDS:
        start, count = now, 0
    _LOGIN_FAILURES[username] = (start, count + 1)


def clear_login_failures(username):
    _LOGIN_FAILURES.pop(username, None)


def create_session(con, username):
    raw = secrets.token_urlsafe(32)
    token_hash = hashlib.sha256(raw.encode()).hexdigest()
    expires = ph_now() + timedelta(days=SESSION_DAYS)
    con.execute("DELETE FROM sessions WHERE expires_at < ?", (now_iso(),))
    con.execute("INSERT INTO sessions(token_hash,username,expires_at,created_at) VALUES(?,?,?,?)",
                (token_hash, username, expires.isoformat(timespec="seconds"), now_iso()))
    return raw


def current_user(con, token):
    if not token:
        return None
    token_hash = hashlib.sha256(token.encode()).hexdigest()
    row = con.execute("""SELECT u.* FROM sessions s JOIN users u ON u.username=s.username
                         WHERE s.token_hash=? AND s.expires_at>? AND u.active=1""", (token_hash, now_iso())).fetchone()
    if not row:
        return None
    user = dict(row)
    user["_session_token"] = token
    return user


def log_activity(con, trip_id, action, details="", username=None):
    con.execute("INSERT INTO activity_log(trip_id,username,action,details,created_at) VALUES(?,?,?,?,?)",
                (trip_id, username, action, details, now_iso()))


def normalize_text(v, max_len=300):
    return (v or "").strip()[:max_len]


def parse_float(v):
    if not v:
        return None
    try:
        return float(v)
    except ValueError:
        return None


def validate_trip(d):
    errors = []
    for field, label in (("container_no", "Container number"), ("driver_name", "Driver name"), ("contact_no", "Contact number")):
        if not normalize_text(d.get(field)):
            errors.append(f"{label} is required.")
    if d.get("priority") not in PRIORITIES:
        errors.append("Invalid priority.")
    if d.get("shipping_line") and d.get("shipping_line") not in SHIPPING_LINES:
        errors.append("Invalid shipping line.")
    if d.get("status") not in ("Automatic", "On Hold", *STATUSES):
        errors.append("Invalid status.")

    parsed = []
    now = ph_now()
    for key, label in TIMES:
        value = d.get(key)
        if value:
            dt = parse_dt(value)
            if not dt:
                errors.append(f"{label}: invalid date/time.")
            else:
                if dt > now + timedelta(minutes=1):
                    errors.append(f"{label}: date/time cannot be in the future.")
                parsed.append((dt, key, label))
    for a, b in zip(parsed, parsed[1:]):
        if b[0] < a[0]:
            errors.append(f"{b[2]} cannot occur before {a[2]}.")
    deps = [
        ("port_departure", "port_arrival", "Port departure requires port arrival."),
        ("delivery_arrival", "port_departure", "Delivery arrival requires port departure."),
        ("unloading_start", "delivery_arrival", "Unloading start requires delivery arrival."),
        ("unloading_finish", "unloading_start", "Unloading finish requires unloading start."),
        ("delivery_departure", "unloading_finish", "Delivery departure requires unloading finish."),
        ("yard_dropped", "delivery_departure", "Yard dropped requires delivery departure."),
        ("yard_pullout", "yard_dropped", "Yard pullout requires a prior yard dropped event."),
        ("returned_port", "delivery_departure", "Returned to port requires delivery departure."),
    ]
    for later, earlier, msg in deps:
        if d.get(later) and not d.get(earlier):
            errors.append(msg)
    if d.get("returned_port") and d.get("yard_dropped") and not d.get("yard_pullout"):
        errors.append("Returned to port requires a prior yard pullout when the container was dropped in the yard.")
    lat = d.get("latitude")
    lon = d.get("longitude")
    if lat is not None and not (-90 <= lat <= 90):
        errors.append("Latitude must be between -90 and 90.")
    if lon is not None and not (-180 <= lon <= 180):
        errors.append("Longitude must be between -180 and 180.")
    return errors


def latest_milestone(d):
    candidates = []
    for key, label in TIMES:
        dt = parse_dt(d.get(key))
        if dt:
            candidates.append((dt, label))
    if candidates:
        return max(candidates, key=lambda x: x[0])
    created = parse_dt(d.get("created_at"))
    return created, "Record created"


def fmt(value):
    if not value:
        return "—"
    dt = parse_dt(value)
    return dt.strftime("%d %b %Y, %I:%M %p") if dt else value


def input_field(key, label, value="", typ="text", required=False):
    req = " required" if required else ""
    if typ == "date" and value:
        dt = parse_dt(value)
        value = dt.date().isoformat() if dt else value
    return f'<label>{escape(label)}<input type="{typ}" name="{escape(key)}" value="{escape(value or "", quote=True)}"{req}></label>'


def select_field(key, label, choices, value):
    options = "".join(f'<option value="{escape(c,quote=True)}" {"selected" if c==value else ""}>{escape(c or "—")}</option>' for c in choices)
    return f'<label>{escape(label)}<select name="{escape(key)}">{options}</select></label>'


def master_choices(table):
    with closing(db()) as con:
        rows = con.execute(f"SELECT name FROM {table} WHERE active=1 ORDER BY lower(name)").fetchall()
    return [r["name"] for r in rows]


def layout(title, body, user=None, refresh=False):
    if user:
        role = user.get("role", "Viewer")
        account_name = user.get("driver_name") or user.get("username") or "User"
        initials = "".join(x[0] for x in str(account_name).split()[:2]).upper() or "U"
        account_client = user.get("client_name") or ("All accounts" if role == "Admin" else "No client assigned")
        csrf = escape(session_csrf(user))
        account_html = (
            '<details class="account-menu"><summary>'
            f'<span class="account-avatar">{escape(initials[:2])}</span>'
            f'<span class="account-summary"><b>{escape(account_name)}</b><small>{escape(role)}</small></span>'
            '<span class="account-chevron">⌄</span></summary>'
            '<div class="account-dropdown">'
            f'<div class="account-card-head"><span class="account-avatar large">{escape(initials[:2])}</span><div><strong>{escape(account_name)}</strong><span>@{escape(user.get("username", ""))}</span></div></div>'
            f'<div class="account-meta"><span>ROLE</span><b>{escape(role)}</b><span>ACCESS</span><b>{escape(account_client)}</b></div>'
            '<a href="/account" class="account-link">My Account</a>'
            f'<form method="post" action="/logout" class="account-logout"><input type="hidden" name="csrf" value="{csrf}"><button class="linkbtn">Log out</button></form>'
            '</div></details>'
        )

        links = [
            ("Dashboard", "/", "⌂", True),
            ("Trips", "/", "▣", False),
        ]
        if role in ("Admin", "Dispatcher"):
            links.append(("Create Trip", "/new", "+", False))
        links += [("Map View", "/map", "⌖", False), ("Calendar", "/analytics", "□", False)]
        if role == "Admin":
            links += [("Clients", "/master-data", "♙", False), ("Truckers", "/master-data", "▱", False)]
        links += [("Drivers", "/driver", "◉", False), ("Shipping Lines", "/master-data", "▤", False), ("Court Yards", "/master-data", "⌂", False)]
        if role == "Admin":
            links.append(("Users", "/users", "♙", False))
        if role != "Viewer":
            links += [("Activity Log", "/activity", "▤", False), ("Reports", "/analytics", "▥", False)]

        sidebar_items=[]
        for label, href, icon, active in links:
            sidebar_items.append(f'<a class="side-link{" active" if active and title=="Dashboard" else ""}" href="{href}"><span class="side-icon">{icon}</span><span>{label}</span></a>')
        sidebar=''.join(sidebar_items)
        sidebar_status='<div class="sidebar-status"><div class="status-caption">SYSTEM STATUS</div><div class="status-online"><span></span>System Online</div><div class="status-detail">All systems operational</div></div>'
        header_account=account_html
    else:
        sidebar=''
        sidebar_status=''
        header_account=''

    refresh_script = f'<script>setTimeout(()=>location.reload(),{LIVE_REFRESH_SECONDS*1000});</script>' if refresh else ''
    mobile_menu = '<button class="mobile-menu" type="button" onclick="document.body.classList.toggle(\'sidebar-open\')">☰</button>'
    sidebar_html = f'''<aside class="sidebar">
        <div class="sidebar-brand"><div class="brand-main">R.DEVERA</div><div class="brand-sub">LOGISTICS</div></div>
        <div class="sidebar-nav">{sidebar}</div>
        {sidebar_status}
    </aside>''' if user else ''

    html = '''<!doctype html>
<html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>''' + escape(title) + ''' | R.DEVERA LOGISTICS SERVICES</title>
<style>
:root{--bg:#f5f7fb;--surface:#fff;--surface2:#f8fafc;--border:#e4e9f1;--text:#162033;--muted:#718096;--navy:#031b3d;--navy2:#062955;--blue:#0b63f6;--blue2:#1769ff;--teal:#12b7a6;--success:#16a34a;--warning:#d98a00;--danger:#dc2626;--shadow:0 8px 28px rgba(15,23,42,.055)}
*{box-sizing:border-box}html{background:var(--bg)}body{margin:0;font:14px Inter,ui-sans-serif,system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;color:var(--text);background:var(--bg)}
a{color:inherit;text-decoration:none}button,input,select,textarea{font:inherit}.sidebar{position:fixed;inset:0 auto 0 0;width:222px;background:linear-gradient(180deg,#02152f 0%,#031d40 55%,#03264d 100%);color:#fff;z-index:120;display:flex;flex-direction:column;box-shadow:8px 0 28px rgba(2,21,47,.12)}
.sidebar-brand{height:101px;display:flex;flex-direction:column;justify-content:center;padding:0 30px;border-bottom:1px solid rgba(255,255,255,.07)}.brand-main{font-size:27px;font-weight:900;letter-spacing:-1.2px}.brand-sub{font-size:13px;color:#19c7e5;font-weight:850;letter-spacing:.5px;margin-top:-2px}.sidebar-nav{padding:15px 15px 0;display:flex;flex-direction:column;gap:4px;overflow:auto}.side-link{height:44px;display:flex;align-items:center;gap:13px;padding:0 13px;border-radius:8px;color:#f1f5fb;font-size:14px;font-weight:600;transition:.16s}.side-link:hover{background:rgba(37,99,235,.28);color:#fff}.side-link.active{background:linear-gradient(90deg,#1671ff,#0a63ef);box-shadow:0 7px 18px rgba(11,99,246,.22)}.side-icon{width:20px;text-align:center;font-size:19px;opacity:.96}.sidebar-status{margin: auto 16px 24px;padding:17px 15px;border:1px solid rgba(64,135,222,.35);border-radius:9px;background:rgba(1,18,44,.28)}.status-caption{font-size:10px;color:#dce7f8;letter-spacing:.5px;margin-bottom:12px}.status-online{display:flex;align-items:center;gap:9px;font-size:12px;font-weight:750}.status-online span{width:10px;height:10px;border-radius:50%;background:#16d55d;box-shadow:0 0 0 4px rgba(22,213,93,.08)}.status-detail{font-size:10px;color:#e5edf9;margin:9px 0 0 19px}
.topbar{position:fixed;left:222px;right:0;top:0;height:101px;background:rgba(255,255,255,.96);border-bottom:1px solid var(--border);display:flex;align-items:center;padding:0 26px;z-index:100}.top-left{display:flex;align-items:center;gap:22px}.mobile-menu{display:none}.top-title{font-size:17px;font-weight:850;color:#1a2b45}.top-spacer{flex:1}.top-meta{display:flex;align-items:center;gap:18px}.top-meta-block{padding-left:18px;border-left:1px solid var(--border);display:flex;align-items:center;gap:9px}.top-meta-block:first-child{border-left:0}.top-icon{font-size:20px;color:#0f63ed}.top-date{font-size:12px;color:#51627a}.weather-head{display:flex;align-items:center;gap:9px}.weather-head .sun{font-size:24px}.weather-head strong{font-size:13px;display:block}.weather-head small{font-size:11px;color:#718096}.account-menu{position:relative}.account-menu summary{list-style:none;display:flex;align-items:center;gap:9px;padding:5px 4px;cursor:pointer}.account-menu summary::-webkit-details-marker{display:none}.account-avatar{width:34px;height:34px;border-radius:50%;background:#0b63e9;color:#fff;display:inline-flex;align-items:center;justify-content:center;font-size:12px;font-weight:850}.account-avatar.large{width:42px;height:42px}.account-summary{display:flex;flex-direction:column;line-height:1.2}.account-summary b{font-size:13px}.account-summary small{font-size:10px;color:#718096;margin-top:2px}.account-chevron{color:#334155;font-size:16px}.account-dropdown{position:absolute;right:0;top:45px;width:260px;background:#fff;border:1px solid var(--border);border-radius:12px;box-shadow:0 18px 45px rgba(15,23,42,.16);padding:12px;z-index:500}.account-card-head{display:flex;align-items:center;gap:10px;padding:3px 2px 11px;border-bottom:1px solid var(--border)}.account-card-head div{display:flex;flex-direction:column}.account-card-head strong{font-size:13px}.account-card-head span{font-size:10px;color:#718096;margin-top:2px}.account-meta{display:grid;grid-template-columns:65px 1fr;gap:5px 8px;padding:11px 2px;font-size:11px}.account-meta span{font-size:9px;color:#94a3b8;font-weight:850}.account-link,.account-logout{display:block;padding:9px;border-radius:8px;font-size:12px;font-weight:700}.account-link:hover,.account-logout:hover{background:#f4f7fb}.account-logout{border:0;background:transparent;width:100%;text-align:left}.linkbtn{border:0!important;background:transparent!important;box-shadow:none!important;color:#dc2626!important;padding:0!important}
.page{margin-left:222px;padding-top:101px;min-height:100vh}.content{max-width:1500px;margin:0 auto;padding:25px 20px 50px}.page-title{font-size:24px;font-weight:850;margin:0 0 18px}.card{background:#fff;border:1px solid var(--border);border-radius:13px;box-shadow:var(--shadow);margin-bottom:18px}.live{display:inline-flex;align-items:center;gap:8px;background:#ecfdf5;color:#087443;border:1px solid #c9f0dc;border-radius:999px;padding:6px 10px;font-size:10px;font-weight:750;margin-bottom:12px}.live:before{content:"";width:6px;height:6px;border-radius:50%;background:#16a34a}.notice,.ok,.error,.issue{padding:12px 14px;border-radius:10px;margin-bottom:14px;border:1px solid}.notice,.ok{background:#ecfdf3;color:#166534;border-color:#bbf7d0}.error,.issue{background:#fef2f2;color:#991b1b;border-color:#fecaca}
.search-card{padding:0;overflow:hidden}.search-row{display:flex;align-items:center;gap:14px;padding:18px 20px;border-bottom:1px solid #edf0f5}.search-box{height:46px;flex:1;position:relative}.search-box input{height:46px;margin:0;padding:0 46px 0 17px;border:1px solid #d5ddea;border-radius:9px;background:#fff;outline:none;color:#24324a}.search-box input:focus{border-color:#74a6fa;box-shadow:0 0 0 3px rgba(11,99,246,.08)}.search-box:after{content:"⌕";position:absolute;right:15px;top:8px;font-size:25px;color:#64748b}.filter-btn,.clear-btn,.new-btn{height:46px;padding:0 17px;border-radius:9px;font-weight:800;border:1px solid #d7e0ec;background:#fff;color:#075ce7;cursor:pointer;display:inline-flex;align-items:center;justify-content:center;gap:8px}.filter-btn:hover,.clear-btn:hover{background:#f3f7ff;border-color:#bdd1f4}.new-btn{background:#0b63f6;color:#fff;border-color:#0b63f6;box-shadow:0 8px 18px rgba(11,99,246,.18);margin-left:auto}.new-btn:hover{background:#084dcc}.status-row{display:flex;align-items:center;gap:7px;padding:13px 20px;overflow-x:auto;white-space:nowrap}.status-filter{display:inline-flex;align-items:center;gap:7px;height:39px;padding:0 10px;border:1px solid #e0e6ef;background:#fff;border-radius:8px;color:#39475d;font-size:11px;font-weight:750;transition:.14s}.status-filter:hover{border-color:#bfd1ef;background:#f8fbff;color:#0b63f6}.status-filter.active{background:#0b63f6;border-color:#0b63f6;color:#fff;box-shadow:0 5px 12px rgba(11,99,246,.15)}.count-pill{min-width:21px;height:21px;border-radius:50%;display:inline-flex;align-items:center;justify-content:center;background:#f1f4f8;color:#596579;font-size:10px;font-weight:850}.status-filter.active .count-pill{background:#fff;color:#0b63f6}
.table-card{overflow:hidden}.table-head{height:76px;display:flex;align-items:center;justify-content:space-between;padding:0 20px;border-bottom:1px solid #edf0f5}.table-title{display:flex;align-items:center;gap:11px;font-size:16px;font-weight:850}.table-title-icon{color:#0b63f6;font-size:22px}.columns-btn{height:38px;padding:0 12px;border:1px solid #dbe3ee;border-radius:8px;background:#fff;color:#334155;font-weight:700;cursor:pointer}.table-wrap{overflow-x:auto}.dashboard-table{width:100%;border-collapse:separate;border-spacing:0;min-width:1080px}.dashboard-table th{background:#fbfcfe;color:#516079;font-size:10px;text-transform:none;letter-spacing:0;padding:13px 11px;border-bottom:1px solid #e9edf3;white-space:nowrap}.dashboard-table td{padding:15px 11px;border-bottom:1px solid #edf0f4;color:#2f3c50;font-size:12px;vertical-align:middle}.dashboard-table tbody tr:hover{background:#fbfdff}.container-link{color:#0865ed;font-size:13px;font-weight:850}.cargo-chip{display:inline-flex;margin-top:6px;padding:4px 7px;border-radius:5px;background:#e9f2ff;color:#0d66ea;font-size:9px;font-weight:800}.driver-cell strong{font-weight:750;color:#334155}.driver-phone{display:block;margin-top:4px;color:#718096;font-size:10px}.shipping-cell{font-weight:750;white-space:nowrap}.shipping-dot{display:inline-flex;width:19px;height:19px;border-radius:3px;align-items:center;justify-content:center;background:#08a7c7;color:#fff;font-size:11px;margin-right:6px}.status-chip{display:inline-flex;align-items:center;gap:6px;border-radius:7px;padding:6px 9px;font-size:10px;font-weight:800;white-space:nowrap}.status-chip:before{content:"";width:7px;height:7px;border-radius:50%;background:currentColor}.status-returned{background:#f2eaff;color:#6b21d8}.status-completed{background:#eaf9ef;color:#16813d}.status-transit{background:#eaf3ff;color:#1764d8}.status-port{background:#edf7ff;color:#1670c4}.status-yard{background:#fff6df;color:#a16600}.status-delivery{background:#eefaf8;color:#078a79}.status-unloading{background:#fff0f0;color:#c13c3c}.status-dispatched{background:#eef2f7;color:#596579}.status-hold{background:#fff0f0;color:#c13c3c}.priority-chip{display:inline-flex;align-items:center;gap:5px;background:#fff8e5;border:1px solid #f4d992;color:#9a6900;border-radius:7px;padding:5px 8px;font-size:10px;font-weight:750;white-space:nowrap}.priority-chip:before{content:"";width:6px;height:6px;border-radius:50%;background:#efa800}.location-cell{white-space:nowrap}.milestone-cell strong{display:block;color:#334155;font-size:11px}.milestone-cell small{display:block;color:#718096;margin-top:4px;font-size:10px}.action-buttons{display:flex;align-items:center;gap:7px}.action-btn{display:inline-flex;align-items:center;justify-content:center;height:36px;padding:0 12px;border-radius:8px;border:1px solid #d8e2ee;background:#fff;color:#0965eb;font-size:11px;font-weight:800;white-space:nowrap}.action-btn:hover{background:#f2f7ff;border-color:#bfd4f6}.action-menu{position:relative}.action-menu summary{list-style:none;height:36px;width:36px;border:1px solid #d8e2ee;border-radius:8px;display:flex;align-items:center;justify-content:center;color:#334155;cursor:pointer}.action-menu summary::-webkit-details-marker{display:none}.action-menu-items{position:absolute;right:0;top:42px;z-index:50;min-width:150px;background:#fff;border:1px solid var(--border);border-radius:9px;box-shadow:0 14px 35px rgba(15,23,42,.13);overflow:hidden}.action-menu-items a{display:block;padding:10px 12px;font-size:11px}.action-menu-items a:hover{background:#f5f8fc;color:#0b63f6}.pagination{height:84px;display:flex;align-items:center;justify-content:space-between;padding:0 20px;color:#526176;font-size:12px}.page-controls{display:flex;align-items:center;gap:8px}.page-btn{width:38px;height:38px;border:1px solid #dbe3ee;background:#fff;border-radius:8px;color:#9aa5b5;font-weight:800}.page-number{width:38px;height:38px;border:1px solid #0b63f6;background:#fff;border-radius:8px;color:#0b63f6;font-weight:850}.per-page{height:38px;border:1px solid #dbe3ee;border-radius:8px;background:#fff;padding:0 11px;color:#334155;font-weight:700}.empty{padding:55px;text-align:center;color:#94a3b8}.muted{color:#718096;font-size:11px}.small{font-size:10px;color:#94a3b8}
.statgrid{display:none}.toolbar{display:flex;gap:10px;align-items:end}.toolbar label{font-weight:700;color:#334155;flex:1}.toolbar input,.toolbar select,.toolbar textarea{width:100%;margin-top:6px}.toolbar button,.button{height:42px;padding:0 15px;border-radius:9px;border:0;background:#0b63f6;color:#fff;font-weight:800}.button.secondary{background:#eef2f7;color:#334155}.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));gap:14px}input,select,textarea{border:1px solid #d8e0eb;border-radius:9px;padding:10px 12px;background:#fff;color:#172033;outline:none}input:focus,select:focus,textarea:focus{border-color:#76a8fb;box-shadow:0 0 0 3px rgba(11,99,246,.08)}label{display:block;font-weight:650;color:#334155}textarea{min-height:90px;resize:vertical}.wide{grid-column:1/-1}h2{font-size:24px;letter-spacing:-.6px;margin:0 0 18px}h3{font-size:16px;margin:0 0 14px}.info-card,.dashboard-info-grid{display:none}
@media(max-width:1100px){.top-date{display:none}.top-meta{gap:8px}.content{padding:20px 16px}.search-row{flex-wrap:wrap}.search-box{min-width:260px}.new-btn{margin-left:auto}}
@media(max-width:800px){.sidebar{transform:translateX(-100%);transition:.2s}.sidebar-open .sidebar{transform:translateX(0)}.topbar{left:0;height:72px;padding:0 15px}.page{margin-left:0;padding-top:72px}.mobile-menu{display:inline-flex;width:38px;height:38px;border:0;border-radius:8px;background:#f2f5f9;color:#24324a;align-items:center;justify-content:center;cursor:pointer}.top-title{font-size:14px}.top-meta-block.weather-block{display:none}.account-summary{display:none}.content{padding:16px 12px 35px}.search-row{padding:14px;gap:8px}.search-box{width:100%;flex-basis:100%}.filter-btn,.clear-btn,.new-btn{height:40px}.new-btn{margin-left:auto}.status-row{padding:10px 14px}.status-filter{height:36px}.table-head{height:64px;padding:0 14px}.pagination{padding:0 14px}.sidebar-open:after{content:"";position:fixed;inset:0;background:rgba(0,0,0,.35);z-index:110}.sidebar{z-index:120}}
@media(max-width:520px){.filter-btn,.clear-btn{padding:0 11px;font-size:11px}.new-btn{padding:0 12px}.pagination{height:auto;padding:14px;gap:12px;flex-wrap:wrap}.page-controls{margin-left:auto}}
</style></head><body>''' + sidebar_html + '''
<div class="topbar"><div class="top-left">''' + mobile_menu + '''<div class="top-title">LOGISTICS CONTROL CENTER</div></div><div class="top-spacer"></div><div class="top-meta">'''
    if user:
        html += '<div class="top-meta-block"><span class="top-icon">◷</span><span id="live-date" class="top-date">Loading...</span></div><div class="top-meta-block weather-block"><div class="weather-head"><span class="sun">☀</span><div><strong id="top-temp">29°C</strong><small id="top-location">Manila, PH</small></div></div></div>' + header_account
    html += '''</div></div><div class="page"><main class="content">''' + body + '''</main></div>''' + refresh_script + '''
<script>(function(){function clock(){const n=new Date(),d=document.getElementById("live-date");if(d)d.textContent=n.toLocaleDateString("en-PH",{timeZone:"Asia/Manila",month:"short",day:"numeric",year:"numeric",hour:"2-digit",minute:"2-digit",hour12:true})+" (PHT)";}clock();setInterval(clock,1000);})();</script></body></html>'''
    return html

def app_secret():
    if APP_SECRET:
        return APP_SECRET.encode()
    secret_path = ROOT / ".truck_monitor_secret"
    try:
        if secret_path.exists():
            value = secret_path.read_bytes()
            if len(value) >= 32:
                return value
        value = secrets.token_bytes(32)
        flags = getattr(os, "O_WRONLY", 1) | getattr(os, "O_CREAT", 64) | getattr(os, "O_EXCL", 128)
        try:
            fd = os.open(secret_path, flags, 0o600)
            with os.fdopen(fd, "wb") as fh:
                fh.write(value)
        except FileExistsError:
            value = secret_path.read_bytes()
        return value
    except OSError:
                                                                                                
        if not hasattr(app_secret, "_runtime"):
            app_secret._runtime = secrets.token_bytes(32)
        return app_secret._runtime


def session_csrf(user):
    session_token = user.get("_session_token") if user else None
    if not session_token:
        return ""
    return hmac.new(app_secret(), session_token.encode(), hashlib.sha256).hexdigest()


def require_csrf(form, user):
    expected = session_csrf(user)
    supplied = form.get("csrf", [""])[0]
    return bool(expected) and hmac.compare_digest(supplied, expected)


def clean_form(raw, key):
    return normalize_text(raw.get(key, [""])[0], 5000)


def parse_form(raw_bytes):
    data = parse_qs(raw_bytes.decode("utf-8"), keep_blank_values=True)
    item = {k: clean_form(data, k) for k in [
        "container_no","driver_name","trucker_name","contact_no","priority","current_location","court_yard_name",
        "cargo_type","shipping_line","client","tags","notes","status","latitude","longitude","assigned_user"
    ]}
    for key, _ in TIMES:
        item[key] = clean_form(data, key)
    item["latitude"] = parse_float(item["latitude"])
    item["longitude"] = parse_float(item["longitude"])
    return item, data


def normalize_record(item):
    x = dict(item)
    x["priority"] = x.get("priority") or "Normal"
    if x.get("status") not in ("On Hold",):
        x["status"] = "Automatic"
    return x


def dashboard_data(con, q="", selected_status="", user=None):
    rows = visible_trips(con, user)
    filtered = []
    ql = q.lower()
    counts = {s:0 for s in STATUSES}
    for d in rows:
        st = effective_status(d); counts[st] = counts.get(st,0)+1
        searchable = " ".join(str(d.get(k) or "") for k in ["container_no","driver_name","trucker_name","shipping_line","tags","client","current_location","court_yard_name","cargo_type","notes","assigned_user"])
        if ql and ql not in searchable.lower():
            continue
        if selected_status and st != selected_status:
            continue
        d["display_status"] = st
        latest_dt, latest_label = latest_milestone(d)
        d["latest_label"] = latest_label
        d["latest_time"] = latest_dt.isoformat(timespec="minutes") if latest_dt else ""
        filtered.append(d)
    return rows, filtered, counts


def dashboard(query, user, notice=""):
    q = query.get("q", [""])[0].strip()
    status = query.get("status", [""])[0]
    if status not in STATUSES:
        status = ""
    with closing(db()) as con:
        rows, filtered, counts = dashboard_data(con, q, status, user)

    is_viewer = user["role"] == "Viewer"
    status_items = [("All", len(rows), "")] + [(s, counts.get(s, 0), s) for s in STATUSES]
    status_html = []
    for label, count, value in status_items:
        params = {"q": q} if q else {}
        if value:
            params["status"] = value
        href = "/?" + urlencode(params) if params else "/"
        active = " active" if value == status else ""
        status_html.append(f'<a class="status-filter{active}" href="{escape(href, quote=True)}"><span>{escape(label)}</span><span class="count-pill">{count}</span></a>')

    rows_html=[]
    for d in filtered:
        st=d["display_status"]
        status_class={
            "Returned to Port":"status-returned","Completed":"status-completed","In Transit":"status-transit",
            "At Port":"status-port","In Court Yard":"status-yard","At Delivery Site":"status-delivery",
            "Unloading":"status-unloading","Dispatched":"status-dispatched","On Hold":"status-hold"
        }.get(st,"status-dispatched")
        cargo=(d.get("cargo_type") or "").replace("Containarized ","") or "—"
        client=d.get("client") or "No client"
        driver=d.get("driver_name") or "—"
        phone=d.get("contact_no") or "—"
        trucker=d.get("trucker_name") or "—"
        shipping=d.get("shipping_line") or "—"
        location=d.get("current_location") or d.get("court_yard_name") or "—"
        latest_label=d.get("latest_label") or "Record created"
        latest_time=fmt(d.get("latest_time")) if d.get("latest_time") else "—"
        priority=d.get("priority") or "Normal"
        can_edit = user["role"] in ("Admin","Dispatcher") or (user["role"]=="Driver" and (not d.get("assigned_user") or d.get("assigned_user")==user["username"]))
        actions=f'<div class="action-buttons"><a class="action-btn" href="/trip/{d["id"]}">◉&nbsp; View</a>'
        if can_edit:
            actions += f'<details class="action-menu"><summary>⌄</summary><div class="action-menu-items"><a href="/trip/{d["id"]}/edit">Edit trip</a><a href="/trip/{d["id"]}">Open details</a></div></details>'
        actions += '</div>'
        trucker_cell = "" if is_viewer else f'<td>{escape(trucker)}</td>'
        rows_html.append(f'''<tr data-trip-id="{d['id']}">
<td><a class="container-link" href="/trip/{d['id']}">{escape(d['container_no'])}</a><span class="cargo-chip">{escape(cargo)}</span></td>
<td class="driver-cell"><strong>{escape(driver)}</strong><span class="driver-phone">{escape(phone)}</span></td>
{trucker_cell}
<td class="shipping-cell"><span class="shipping-dot">✦</span>{escape(shipping)}</td>
<td><span class="status-chip {status_class}">{escape(st)}</span></td>
<td><span class="priority-chip">{escape(priority)}</span></td>
<td class="location-cell">{escape(location)}</td>
<td class="milestone-cell"><strong>{escape(latest_label)}</strong><small>{escape(latest_time)}</small></td>
<td class="actions-cell">{actions}</td>
</tr>''')

    col_count=9 if is_viewer else 10
    body=(f'<div class="notice">{escape(notice)}</div>' if notice else '') + f'''
<div class="live">Live database view · refreshes every {LIVE_REFRESH_SECONDS} seconds</div>
<div class="card search-card">
  <form method="get" class="search-row">
    <div class="search-box"><input name="q" value="{escape(q, quote=True)}" placeholder="Search container, driver, trucker, shipping line..."></div>
    <button class="filter-btn" type="submit">⚱&nbsp; Filter</button>
    <a class="clear-btn" href="/">◴&nbsp; Clear</a>
    {('<a class="new-btn" href="/new">＋&nbsp; New Trip</a>' if user["role"] in ("Admin","Dispatcher") else '')}
  </form>
  <div class="status-row">{''.join(status_html)}</div>
</div>
<div class="card table-card">
  <div class="table-head"><div class="table-title"><span class="table-title-icon">▣</span>Trips <span class="muted">({len(filtered)})</span></div><button class="columns-btn" type="button">▦&nbsp; Columns⌄</button></div>
  <div class="table-wrap"><table class="dashboard-table {('viewer-table' if is_viewer else '')}">
    <thead><tr><th>Container No.</th><th>Driver</th>{'' if is_viewer else '<th>Trucker</th>'}<th>Shipping Line</th><th>Status</th><th>Priority</th><th>Current Location</th><th>Latest Milestone</th><th>Time</th><th>Actions</th></tr></thead>
    <tbody>{''.join(rows_html) or f'<tr><td colspan="{col_count}" class="empty">No trips found.</td></tr>'}</tbody>
  </table></div>
  <div class="pagination"><span>Showing 1 to {len(filtered)} of {len(filtered)} trips</span><div class="page-controls"><button class="page-btn" disabled>‹</button><button class="page-number">1</button><button class="page-btn" disabled>›</button><select class="per-page"><option>10 / page</option><option>25 / page</option><option>50 / page</option></select></div></div>
</div>
'''
    return layout("Dashboard", body, user, refresh=False)

def trip_form(row,user,error=""):
    r=dict(row or {}); is_edit=bool(row)
    if user["role"]=="Driver" and is_edit and r.get("assigned_user") not in (None,"",user["username"]):
        return layout("Forbidden",'<div class="error">You can only update trips assigned to your driver account.</div>',user)
    status_exception = "On Hold" if r.get("status")=="On Hold" else "Automatic"
    choices=list(CARGO_TYPES)
    if r.get("cargo_type") and r["cargo_type"] not in choices: choices.insert(1,r["cargo_type"])
    err=f'<div class="error">{escape(error).replace(chr(10),"<br>")}</div>' if error else ''
    can_assign=user["role"] in ("Admin","Dispatcher")
    assigned_field=input_field("assigned_user","Assigned account",r.get("assigned_user")) if can_assign else f'<input type="hidden" name="assigned_user" value="{escape(r.get("assigned_user") or (user["username"] if user["role"]=="Driver" else ""),quote=True)}">'
    body=f'''<div class="card"><h2>{"Update trip" if is_edit else "Register a truck trip"}</h2>{err}
<form method="post" class="grid"> <input type="hidden" name="csrf" value="{escape(session_csrf(user))}">
{input_field('container_no','Container number',r.get('container_no'),required=True)}{input_field('driver_name','Driver name',r.get('driver_name'),required=True)}{select_field('trucker_name','Trucker',[''] + master_choices('truckers'),r.get('trucker_name'))}{input_field('contact_no','Contact number',r.get('contact_no'),required=True)}
{select_field('client','Consignee / Client',[''] + master_choices('clients'),r.get('client'))}{select_field('shipping_line','Shipping Line',[''] + SHIPPING_LINES,r.get('shipping_line'))}{select_field('cargo_type','Cargo type',choices,r.get('cargo_type'))}{input_field('court_yard_name','Court Yard name',r.get('court_yard_name'))}{input_field('current_location','Current location',r.get('current_location'))}{select_field('priority','Priority',PRIORITIES,r.get('priority','Normal'))}{select_field('status','Status exception',['Automatic','On Hold'],status_exception)}
{assigned_field}{input_field('latitude','Latitude',r.get('latitude') or '', 'number')}{input_field('longitude','Longitude',r.get('longitude') or '', 'number')}
<div class="wide"><h3>Movement milestones</h3><div class="grid">{''.join(input_field(k,label,r.get(k),"datetime-local") for k,label in TIMES)}</div></div>
{input_field('tags','Custom tags (comma separated)',r.get('tags'))}<div class="wide"><label>Notes / exception details<textarea name="notes">{escape(r.get('notes') or '')}</textarea></label></div>
<div class="wide"><button>{"Save changes" if is_edit else "Register trip"}</button> <a href="/">Cancel</a></div></form></div>'''
    return layout("Update trip" if is_edit else "New Trip",body,user)


def detail(row,user):
    r=dict(row); status=effective_status(r); latest_dt,latest_label=latest_milestone(r)
    events=''.join(f'<tr><td>{escape(label)}</td><td>{escape(fmt(r.get(k)))}</td></tr>' for k,label in TIMES)
    with closing(db()) as con:
        activity=con.execute("SELECT * FROM activity_log WHERE trip_id=? ORDER BY id DESC LIMIT 100",(r["id"],)).fetchall()
    activity_html=''.join(f'<tr><td>{escape(fmt(a["created_at"]))}</td><td>{escape(a["username"] or "system")}</td><td>{escape(a["action"])}</td><td>{escape(a["details"] or "")}</td></tr>' for a in activity)
    edit = f'<a class="button" href="/trip/{r["id"]}/edit">Update trip</a>' if user["role"] in ("Admin","Dispatcher") or (user["role"]=="Driver" and r.get("assigned_user") in (None,"",user["username"])) else ''
    body=f'''<div class="card"><a href="/">← Dashboard</a><div class="toolbar" style="margin-top:12px"><div><h2 style="margin:0">{escape(r['container_no'])}</h2><span class="tag status">{escape(status)}</span> <span class="tag">{escape(r.get('priority') or 'Normal')}</span></div><div>{edit}</div></div></div>
<div class="grid"><div class="card"><h3>Truck & delivery</h3><p><b>Driver:</b> {escape(r['driver_name'])}<br><b>Contact:</b> {escape(r['contact_no'])}<br><b>Client:</b> {escape(r.get('client') or '—')}<br><b>Shipping Line:</b> {escape(r.get('shipping_line') or '—')}<br><b>Cargo:</b> {escape(r.get('cargo_type') or '—')}<br><b>Court Yard:</b> {escape(r.get('court_yard_name') or '—')}<br><b>Location:</b> {escape(r.get('current_location') or '—')}<br><b>Coordinates:</b> {escape(str(r.get('latitude') or '—'))}, {escape(str(r.get('longitude') or '—'))}<br><b>Assigned:</b> {escape(r.get('assigned_user') or '—')}<br><b>Latest:</b> {escape(latest_label)} — {escape(fmt(latest_dt.isoformat(timespec='minutes') if latest_dt else ''))}</p><h3>Notes</h3><p>{escape(r.get('notes') or '—')}</p></div>
<div class="card"><h3>Movement timeline</h3><table><tr><th>Milestone</th><th>Date & time</th></tr>{events}</table></div></div>
<div class="card"><h3>Activity history</h3><div class="table-wrap"><table><tr><th>Time</th><th>User</th><th>Action</th><th>Details</th></tr>{activity_html or '<tr><td colspan="4">No activity.</td></tr>'}</table></div></div>'''
    return layout(r["container_no"],body,user)


def analytics_page(user):
    with closing(db()) as con:
        rows=visible_trips(con,user)
    counts={s:0 for s in STATUSES}; drivers={}; clients={}; completed=[]; unloading=[]
    for d in rows:
        st=effective_status(d); counts[st]=counts.get(st,0)+1
        drivers[d["driver_name"]]=drivers.get(d["driver_name"],0)+1
        if d.get("client"): clients[d["client"]]=clients.get(d["client"],0)+1
        a=parse_dt(d.get("delivery_arrival")); b=parse_dt(d.get("delivery_departure"))
        if a and b: completed.append((b-a).total_seconds()/3600)
        a=parse_dt(d.get("unloading_start")); b=parse_dt(d.get("unloading_finish"))
        if a and b: unloading.append((b-a).total_seconds()/3600)
    avg_delivery=sum(completed)/len(completed) if completed else 0; avg_unload=sum(unloading)/len(unloading) if unloading else 0
    driver_html=''.join(f'<tr><td>{escape(k)}</td><td>{v}</td></tr>' for k,v in sorted(drivers.items(),key=lambda x:(-x[1],x[0]))[:20])
    client_html=''.join(f'<tr><td>{escape(k)}</td><td>{v}</td></tr>' for k,v in sorted(clients.items(),key=lambda x:(-x[1],x[0]))[:20])
    body=f'''<h2>Analytics</h2><div class="statgrid"><div class="stat"><span class="muted">Total trips</span><strong>{len(rows)}</strong></div><div class="stat"><span class="muted">Completed</span><strong>{counts.get('Completed',0)}</strong></div><div class="stat"><span class="muted">Active</span><strong>{sum(v for k,v in counts.items() if k not in ('Completed','Returned to Port'))}</strong></div><div class="stat"><span class="muted">Urgent</span><strong>{sum(1 for x in rows if x.get('priority')=='Urgent')}</strong></div><div class="stat"><span class="muted">Avg delivery hours</span><strong>{avg_delivery:.1f}</strong></div><div class="stat"><span class="muted">Avg unloading hours</span><strong>{avg_unload:.1f}</strong></div></div><div class="grid"><div class="card"><h3>Status distribution</h3><table><tr><th>Status</th><th>Trips</th></tr>{''.join(f'<tr><td>{escape(s)}</td><td>{counts.get(s,0)}</td></tr>' for s in STATUSES)}</table></div><div class="card"><h3>Trips by driver</h3><table><tr><th>Driver</th><th>Trips</th></tr>{driver_html or '<tr><td colspan="2">—</td></tr>'}</table></div><div class="card"><h3>Trips by client</h3><table><tr><th>Client</th><th>Trips</th></tr>{client_html or '<tr><td colspan="2">—</td></tr>'}</table></div></div>'''
    return layout("Analytics",body,user)


def alerts_page(user):
    with closing(db()) as con:
        rows=visible_trips(con,user)
    now=datetime.now(); alerts=[]
    for d in rows:
        st=effective_status(d)
        if d.get("priority")=="Urgent" and st not in ("Completed","Returned to Port"):
            alerts.append(("URGENT",d,f"Urgent trip is still active ({st})."))
        latest,_=latest_milestone(d)
        if latest and st not in ("Completed","Returned to Port") and now-latest>timedelta(hours=8):
            alerts.append(("DELAY",d,f"No new movement for {(now-latest).total_seconds()/3600:.1f} hours."))
        if st=="Unloading":
            start=parse_dt(d.get("unloading_start"))
            if start and now-start>timedelta(hours=4): alerts.append(("UNLOADING",d,"Unloading has exceeded 4 hours."))
    html=''.join(f'<div class="issue"><b>{escape(level)}</b> · <a href="/trip/{d["id"]}">{escape(d["container_no"])}</a> — {escape(msg)}</div>' for level,d,msg in alerts)
    body=f'<h2>Alerts</h2>{html or "<div class=ok>No active alerts.</div>"}'
    return layout("Alerts",body,user)


def activity_page(user):
    with closing(db()) as con:
        rows=con.execute("SELECT a.*,t.container_no FROM activity_log a LEFT JOIN trips t ON t.id=a.trip_id ORDER BY a.id DESC LIMIT 300").fetchall()
    html=''.join(f'<tr><td>{escape(fmt(r["created_at"]))}</td><td>{escape(r["username"] or "system")}</td><td>{escape(r["container_no"] or "-")}</td><td>{escape(r["action"])}</td><td>{escape(r["details"] or "")}</td></tr>' for r in rows)
    return layout("Activity Log",f'<div class="card"><h2>Activity Log</h2><div class="table-wrap"><table><tr><th>Time</th><th>User</th><th>Container</th><th>Action</th><th>Details</th></tr>{html or "<tr><td colspan=5>No activity.</td></tr>"}</table></div></div>',user)


def audit_page(user):
    with closing(db()) as con:
        rows=[dict(r) for r in con.execute("SELECT * FROM trips ORDER BY id").fetchall()]
        if USE_POSTGRES:
            columns={r["column_name"] for r in con.execute("SELECT column_name FROM information_schema.columns WHERE table_schema='public' AND table_name='trips'").fetchall()}
            integrity="ok"
            foreign_keys=[]
        else:
            columns={r["name"] for r in con.execute("PRAGMA table_info(trips)")}
            integrity=con.execute("PRAGMA integrity_check").fetchone()[0]
            foreign_keys=con.execute("PRAGMA foreign_key_check").fetchall()
    issues=[]; seen={}
    if integrity != "ok":
        issues.append(("PostgreSQL" if USE_POSTGRES else "SQLite") + " integrity check failed: " + str(integrity))
    if foreign_keys:
        issues.append(f"Foreign key violations found: {len(foreign_keys)}.")
    required={"id","container_no","driver_name","trucker_name","contact_no","status","priority","current_location","court_yard_name","cargo_type","shipping_line","client",*TIME_KEYS,"tags","notes","created_at","updated_at","latitude","longitude","last_location_at","assigned_user","created_by","updated_by"}
    missing=required-columns
    if missing: issues.append("Missing database columns: "+", ".join(sorted(missing)))
    user_names = set()
    client_names = set()
    trucker_names = set()
    with closing(db()) as con2:
        user_names = {r["username"].casefold() for r in con2.execute("SELECT username FROM users").fetchall()}
        client_names = {r["name"].casefold() for r in con2.execute("SELECT name FROM clients").fetchall()}
        trucker_names = {r["name"].casefold() for r in con2.execute("SELECT name FROM truckers").fetchall()}
    now = ph_now()
    for d in rows:
        c=d.get("container_no",""); seen[c]=seen.get(c,0)+1
        expected=effective_status(d)
        if d.get("status")!=expected: issues.append(f"{c}: stored status '{d.get('status')}' != calculated '{expected}'.")
        issues.extend(f"{c}: {e}" for e in validate_trip(d) if e not in ("Container number is required.","Driver name is required.","Contact number is required.","Invalid priority.","Invalid status."))
        if d.get("assigned_user") and d["assigned_user"].casefold() not in user_names:
            issues.append(f"{c}: assigned account '{d['assigned_user']}' does not exist.")
        if d.get("client") and d["client"].casefold() not in client_names:
            issues.append(f"{c}: client '{d['client']}' is missing from master data.")
        if d.get("trucker_name") and d["trucker_name"].casefold() not in trucker_names:
            issues.append(f"{c}: trucker '{d['trucker_name']}' is missing from master data.")
        for key, label in TIMES:
            dt=parse_dt(d.get(key))
            if dt and dt > now + timedelta(minutes=1):
                issues.append(f"{c}: {label} is in the future.")
        if d.get("returned_port") and d.get("yard_dropped") and not d.get("yard_pullout"):
            issues.append(f"{c}: returned to port is recorded after yard drop without yard pullout.")
    for c,n in seen.items():
        if n>1: issues.append(f"{c}: duplicate container number ({n}).")
    body=f'<div class="card"><h2>Database Consistency Audit</h2><p><b>Records:</b> {len(rows)} · <b>Issues:</b> {len(issues)}</p>{"<div class=ok>No conflicts found. Dashboard status is derived from the same authoritative event timestamps stored in the database.</div>" if not issues else ""}{"".join(f"<div class=issue>{escape(x)}</div>" for x in issues)}</div>'
    return layout("Database Audit",body,user)


def account_page(user, notice="", error=""):
    with closing(db()) as con:
        r=con.execute("SELECT username,role,driver_name,client_name,active,created_at FROM users WHERE username=?",(user["username"],)).fetchone()
    if not r: return layout("My Account",'<div class="error">Account not found.</div>',user)
    display_name=r["driver_name"] or r["username"]
    initials="".join(x[0] for x in str(display_name).split()[:2]).upper() or "U"
    client=r["client_name"] or ("All accounts" if r["role"]=="Admin" else "No client assigned")
    msg=(f'<div class="ok">{escape(notice)}</div>' if notice else "")+(f'<div class="error">{escape(error)}</div>' if error else "")
    body=f'''{msg}<div class="account-page-grid"><div class="card account-profile-card"><div class="profile-hero"><span class="account-avatar profile-avatar">{escape(initials[:2])}</span><div><h2>{escape(display_name)}</h2><p>@{escape(r["username"])}</p></div></div><div class="profile-info"><div><span>ROLE</span><strong>{escape(r["role"])}</strong></div><div><span>CONSIGNEE / CLIENT</span><strong>{escape(client)}</strong></div><div><span>ACCOUNT STATUS</span><strong>{"Active" if r["active"] else "Disabled"}</strong></div><div><span>CREATED</span><strong>{escape(fmt(r["created_at"]))}</strong></div></div></div><div class="card"><h2>Security</h2><p class="muted">Change your own password.</p><form method="post" action="/account" class="grid"><input type="hidden" name="csrf" value="{escape(session_csrf(user))}"><input type="hidden" name="action" value="password">{input_field("current_password","Current password",required=True)}{input_field("new_password","New password",required=True)}{input_field("confirm_password","Confirm new password",required=True)}<div class="wide"><button>Update password</button></div></form></div></div>'''
    return layout("My Account",body,user)


def users_page(user, notice=""):
    if user["role"]!="Admin":
        return layout("Forbidden",'<div class=error>Admin access required.</div>',user)
    with closing(db()) as con:
        rows=con.execute("SELECT id,username,role,driver_name,client_name,active,created_at FROM users ORDER BY username").fetchall()
    html=''.join(
        f'''<tr><td>{escape(r["username"])}</td><td>{escape(r["role"])}</td><td>{escape(r["driver_name"] or "")}</td><td>{escape(r["client_name"] or "—")}</td><td>{"Active" if r["active"] else "Disabled"}</td><td>{escape(fmt(r["created_at"]))}</td><td><div class="admin-actions"><a class="button secondary" href="/users/edit?id={r["id"]}">Edit</a><form method="post" action="/users" class="inline" onsubmit="return confirm('Delete this user?');"><input type="hidden" name="csrf" value="{escape(session_csrf(user))}"><input type="hidden" name="action" value="delete"><input type="hidden" name="id" value="{r["id"]}"><button type="submit" class="danger">Delete</button></form></div></td></tr>'''
        for r in rows
    ) or '<tr><td colspan="7" class="muted">No users found.</td></tr>'
    client_choices=[''] + master_choices('clients')
    msg=f'<div class="ok">{escape(notice)}</div>' if notice else ""
    body=f'''{msg}<div class="card"><h2>User Management</h2>
<p class="muted">For a Viewer account, select the Consignee / Client whose trips this account is allowed to see.</p>
<form method="post" action="/users" class="grid">
<input type="hidden" name="csrf" value="{escape(session_csrf(user))}"><input type="hidden" name="action" value="create">
{input_field('username','Username',required=True)}{input_field('password','Temporary password',required=True)}
{select_field('role','Role',ROLES,'Viewer')}{input_field('driver_name','Driver name (for Driver role)')}
{select_field('client_name','Consignee / Client (for Viewer)',client_choices,'')}
<div class="wide"><button>Create user</button></div></form></div>
<div class="card"><div class="table-wrap"><table><tr><th>Username</th><th>Role</th><th>Driver name</th><th>Consignee / Client</th><th>Status</th><th>Created</th><th>Actions</th></tr>{html}</table></div></div>'''
    return layout("Users",body,user)


def user_edit_page(user, ident, error=""):
    if user["role"]!="Admin":
        return layout("Forbidden",'<div class=error>Admin access required.</div>',user)
    with closing(db()) as con:
        r=con.execute("SELECT id,username,role,driver_name,client_name,active FROM users WHERE id=?",(ident,)).fetchone()
    if not r: return layout("Not found",'<div class=error>User not found.</div>',user)
    clients=['']+master_choices('clients')
    msg=f'<div class="error">{escape(error)}</div>' if error else ""
    body=f'''<div class="card" style="max-width:800px;margin:auto">{msg}<h2>Edit User</h2>
<form method="post" action="/users" class="grid"><input type="hidden" name="csrf" value="{escape(session_csrf(user))}"><input type="hidden" name="action" value="edit"><input type="hidden" name="id" value="{r["id"]}">
{input_field("username","Username",r["username"],required=True)}{input_field("password","New password (leave blank to keep current)")}
{select_field("role","Role",ROLES,r["role"])}{input_field("driver_name","Driver name",r["driver_name"] or "")}
{select_field("client_name","Consignee / Client (for Viewer)",clients,r["client_name"] or "")}{select_field("active","Status",["1","0"],str(r["active"]))}
<div class="wide"><button>Save changes</button> <a class="button secondary" href="/users">Cancel</a></div></form></div>'''
    return layout("Edit User",body,user)


def master_data_page(user, notice=""):
    if user["role"]!="Admin":
        return layout("Forbidden",'<div class="error">Admin access required.</div>',user)
    with closing(db()) as con:
        truckers=con.execute("SELECT id,name,active,created_at FROM truckers ORDER BY lower(name)").fetchall()
        clients=con.execute("SELECT id,name,active,created_at FROM clients ORDER BY lower(name)").fetchall()
    t_html="".join(f'''<tr><td>{escape(r["name"])}</td><td>{"Active" if r["active"] else "Disabled"}</td><td>{escape(fmt(r["created_at"]))}</td><td><div class="admin-actions"><a class="button secondary" href="/master-data/edit?kind=trucker&id={r["id"]}">Edit</a><form method="post" action="/master-data" class="inline" onsubmit="return confirm('Delete this trucker?');"><input type="hidden" name="csrf" value="{escape(session_csrf(user))}"><input type="hidden" name="action" value="delete"><input type="hidden" name="kind" value="trucker"><input type="hidden" name="id" value="{r["id"]}"><button class="danger">Delete</button></form></div></td></tr>''' for r in truckers) or '<tr><td colspan="4" class="muted">No truckers added yet.</td></tr>'
    c_html="".join(f'''<tr><td>{escape(r["name"])}</td><td>{"Active" if r["active"] else "Disabled"}</td><td>{escape(fmt(r["created_at"]))}</td><td><div class="admin-actions"><a class="button secondary" href="/master-data/edit?kind=client&id={r["id"]}">Edit</a><form method="post" action="/master-data" class="inline" onsubmit="return confirm('Delete this client?');"><input type="hidden" name="csrf" value="{escape(session_csrf(user))}"><input type="hidden" name="action" value="delete"><input type="hidden" name="kind" value="client"><input type="hidden" name="id" value="{r["id"]}"><button class="danger">Delete</button></form></div></td></tr>''' for r in clients) or '<tr><td colspan="4" class="muted">No clients added yet.</td></tr>'
    msg=f'<div class="ok">{escape(notice)}</div>' if notice else ""
    body=f'''{msg}<div class="card"><h2>Master Data</h2><div class="grid">
<form method="post" action="/master-data" class="card" style="margin:0"><input type="hidden" name="csrf" value="{escape(session_csrf(user))}"><input type="hidden" name="action" value="create"><input type="hidden" name="kind" value="trucker"><h3>Add Trucker</h3>{input_field("name","Trucker name",required=True)}<div class="master-data-actions"><button>Add Trucker</button></div></form>
<form method="post" action="/master-data" class="card" style="margin:0"><input type="hidden" name="csrf" value="{escape(session_csrf(user))}"><input type="hidden" name="action" value="create"><input type="hidden" name="kind" value="client"><h3>Add Consignee / Client</h3>{input_field("name","Consignee / Client name",required=True)}<div class="master-data-actions"><button>Add Client</button></div></form>
</div></div><div class="grid"><div class="card"><h3>Truckers</h3><div class="table-wrap"><table><tr><th>Name</th><th>Status</th><th>Created</th><th>Actions</th></tr>{t_html}</table></div></div><div class="card"><h3>Consignee / Clients</h3><div class="table-wrap"><table><tr><th>Name</th><th>Status</th><th>Created</th><th>Actions</th></tr>{c_html}</table></div></div></div>'''
    return layout("Master Data",body,user)


def master_data_edit_page(user, kind, ident, error=""):
    if user["role"]!="Admin": return layout("Forbidden",'<div class=error>Admin access required.</div>',user)
    table={"trucker":"truckers","client":"clients"}.get(kind)
    if not table: return layout("Not found",'<div class=error>Invalid type.</div>',user)
    with closing(db()) as con: r=con.execute(f"SELECT id,name,active FROM {table} WHERE id=?",(ident,)).fetchone()
    if not r: return layout("Not found",'<div class=error>Record not found.</div>',user)
    label="Trucker" if kind=="trucker" else "Consignee / Client"
    msg=f'<div class="error">{escape(error)}</div>' if error else ""
    body=f'''<div class="card" style="max-width:650px;margin:auto">{msg}<h2>Edit {label}</h2><form method="post" action="/master-data" class="grid">
<input type="hidden" name="csrf" value="{escape(session_csrf(user))}"><input type="hidden" name="action" value="edit"><input type="hidden" name="kind" value="{kind}"><input type="hidden" name="id" value="{ident}">
{input_field("name",label,r["name"],required=True)}{select_field("active","Status",["1","0"],str(r["active"]))}
<div class="wide"><button>Save changes</button> <a class="button secondary" href="/master-data">Cancel</a></div></form></div>'''
    return layout("Edit Master Data",body,user)


def map_page(user):
    body='''<div class="card"><h2>Live Map</h2><div id="map"></div></div>
<link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css"><script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"></script><script>
const map=L.map('map').setView([14.5995,120.9842],6);L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png',{maxZoom:19,attribution:'© OpenStreetMap contributors'}).addTo(map);
fetch('/api/trips').then(r=>r.json()).then(data=>{const pts=[];data.trips.forEach(t=>{if(t.latitude!=null&&t.longitude!=null){const m=L.marker([t.latitude,t.longitude]).addTo(map);m.bindPopup('<b>'+escapeHtml(t.container_no)+'</b><br>'+escapeHtml(t.display_status)+'<br>'+escapeHtml(t.driver_name));pts.push([t.latitude,t.longitude]);}});if(pts.length)map.fitBounds(pts,{padding:[20,20]});});
function escapeHtml(s){return String(s??'').replace(/[&<>'\"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;',"'":'&#39;','\"':'&quot;'}[c]));}
</script>'''
    return layout("Map",body,user)


def driver_page(user):
    with closing(db()) as con:
        if user["role"] == "Driver":
            rows = [dict(r) for r in con.execute("SELECT * FROM trips WHERE assigned_user=? ORDER BY updated_at DESC", (user["username"],)).fetchall()]
        else:
            rows = visible_trips(con,user)
    cards = []
    rows = [d for d in rows if effective_status(d) not in ("Completed", "Returned to Port")]
    for d in rows:
        st = effective_status(d)
        next_event = next(((k, l) for k, l in TIMES if not d.get(k)), None)
        action = ""
        if next_event and user_can_edit(user, d):
            action = f'<form method="post" action="/trip/{d["id"]}/event/{next_event[0]}"><input type="hidden" name="csrf" value="{escape(session_csrf(user))}"><button style="width:100%;padding:14px">Record: {escape(next_event[1])}</button></form>'
        cards.append(f'''<div class="card"><h3 style="margin-top:0">{escape(d["container_no"])}</h3><span class="tag status">{escape(st)}</span><p><b>Driver:</b> {escape(d["driver_name"])}<br><b>Client:</b> {escape(d.get("client") or "—")}<br><b>Location:</b> {escape(d.get("current_location") or "—")}<br><b>Priority:</b> {escape(d.get("priority") or "Normal")}</p>{action}<p><a class="button" href="/trip/{d["id"]}">Open trip</a></p></div>''')
    body = '<h2>Driver Mobile View</h2><div style="max-width:650px;margin:auto">' + ("".join(cards) or '<div class="ok">No assigned active trips.</div>') + '</div>'
    return layout("Driver", body, user)


def login_page(error=""):
    err=f'<div class="error">{escape(error)}</div>' if error else ''
    return layout("Login",f'<div class="card" style="max-width:430px;margin:60px auto"><h2>Sign in</h2>{err}<form method="post" action="/login"><label>Username<input name="username" required autocomplete="username"></label><label>Password<input type="password" name="password" required autocomplete="current-password"></label><button style="margin-top:12px">Sign in</button></form></div>',None)


def forbidden(user): return layout("Forbidden",'<div class="error">You do not have permission for this action.</div>',user)


def get_trip(con, ident):
    row=con.execute("SELECT * FROM trips WHERE id=?",(ident,)).fetchone()
    return dict(row) if row else None


def validate_milestone_update(old, new):
    errors = []
    for key, label in TIMES:
        before = old.get(key)
        after = new.get(key)
        if before and after and before != after:
            errors.append(f"{label} is already recorded and cannot be changed.")
        elif before and not after:
            errors.append(f"{label} is already recorded and cannot be cleared.")
    return errors


def visible_trips(con, user):
    if user and user["role"] == "Viewer":
        client = normalize_text(user.get("client_name"), 200)
        if not client:
            return []
        return [dict(r) for r in con.execute(
            "SELECT * FROM trips WHERE lower(trim(COALESCE(client,'')))=lower(trim(?)) ORDER BY updated_at DESC,id DESC",
            (client,)
        ).fetchall()]
    return [dict(r) for r in con.execute("SELECT * FROM trips ORDER BY updated_at DESC,id DESC").fetchall()]


def user_can_view_trip(user, row):
    if user["role"] != "Viewer":
        return True
    client = normalize_text(user.get("client_name"), 200)
    row_client = normalize_text(row.get("client"), 200)
    return bool(client) and bool(row_client) and client.casefold() == row_client.casefold()


def user_can_edit(user, row):
    return user["role"] in ("Admin","Dispatcher") or (user["role"]=="Driver" and row.get("assigned_user") in (None,"",user["username"]))


def export_page(query,user):
    start=query.get("start_date",[""])[0].strip(); end=query.get("end_date",[""])[0].strip()
    if not start and not end:
        return layout("Export",f'<div class="card"><h2>Export Trips to CSV</h2><form method="get" action="/export" class="grid">{input_field("start_date","From date","","date",True)}{input_field("end_date","To date","","date",True)}<div class="wide"><button>Export CSV</button></div></form></div>',user)
    try:
        if start: datetime.fromisoformat(start)
        if end: datetime.fromisoformat(end)
    except ValueError: return layout("Export",'<div class=error>Invalid date range.</div>',user)
    if start and end and start>end: start,end=end,start
    cond=[]; params=[]
    if start: cond.append("date(port_arrival)>=date(?)"); params.append(start)
    if end: cond.append("date(port_arrival)<=date(?)"); params.append(end)
    where=" WHERE "+" AND ".join(cond) if cond else ""
    with closing(db()) as con:
        rows=con.execute(f"SELECT * FROM trips{where} ORDER BY port_arrival,id",params).fetchall(); cols=list(rows[0].keys()) if rows else []
    out=io.StringIO(); writer=csv.writer(out); headers=cols+(["Trip Date"] if "Trip Date" not in cols else []); writer.writerow(headers)
    for r in rows: writer.writerow([csv_safe(r[c]) for c in cols]+([csv_safe(r["port_arrival"] or "")] if "Trip Date" not in cols else []))
    data=out.getvalue().encode(); self_response=None
    return data, start, end


def csv_safe(v):
    if isinstance(v,str) and v[:1] in ("=","+","-","@"): return "'"+v
    return v


class Handler(BaseHTTPRequestHandler):
    server_version="TruckMonitor/3.0"

    def headers_security(self):
        self.send_header("X-Content-Type-Options","nosniff")
        self.send_header("X-Frame-Options","SAMEORIGIN")
        self.send_header("Referrer-Policy","strict-origin-when-cross-origin")
        self.send_header("Content-Security-Policy","default-src 'self' https://unpkg.com https://{s}.tile.openstreetmap.org; style-src 'self' 'unsafe-inline' https://unpkg.com; script-src 'self' 'unsafe-inline' https://unpkg.com; img-src 'self' data: https://*.tile.openstreetmap.org")

    def send_html(self,content,code=200,headers=None):
        data=content.encode("utf-8")
        self.send_response(code); self.send_header("Content-Type","text/html; charset=utf-8"); self.send_header("Content-Length",str(len(data))); self.send_header("Cache-Control","no-store"); self.headers_security()
        for k,v in (headers or []): self.send_header(k,v)
        self.end_headers(); self.wfile.write(data)

    def redirect(self,url,token=None):
        self.send_response(303); self.send_header("Location",url); self.send_header("Cache-Control","no-store"); self.headers_security()
        if token:
            cookie=f"session={token}; Path=/; HttpOnly; SameSite=Lax; Max-Age={SESSION_DAYS*86400}" + ("; Secure" if COOKIE_SECURE else "")
            self.send_header("Set-Cookie",cookie)
        self.end_headers()

    def request_user(self):
        cookie=self.headers.get("Cookie",""); token=""
        for part in cookie.split(";"):
            if part.strip().startswith("session="): token=part.strip().split("=",1)[1]
        with closing(db()) as con: return current_user(con,token)

    def require_user(self):
        u=self.request_user()
        if not u:
            self.send_html(login_page(),401); return None
        return u

    def read_form(self):
        try: length=int(self.headers.get("Content-Length","0"))
        except ValueError: raise ValueError("Invalid request length.")
        if length<0 or length>MAX_REQUEST_BYTES: raise ValueError("Request too large.")
        return parse_form(self.rfile.read(length))

    def do_GET(self):
        p=urlparse(self.path); parts=p.path.strip("/").split("/")
        if p.path=="/login": return self.send_html(login_page())
        if p.path=="/health": return self.send_html(json.dumps({"ok":True,"database":"PostgreSQL" if USE_POSTGRES else DB.name}),200,[("Content-Type","application/json")])
        user=self.request_user()
        if not user: return self.redirect("/login")
        if p.path=="/": return self.send_html(dashboard(parse_qs(p.query),user,parse_qs(p.query).get("notice",[""])[0]))
        if user["role"]=="Viewer" and not (len(parts)==2 and parts[0]=="trip" and parts[1].isdigit()):
            return self.send_html(forbidden(user),403)
        if p.path=="/analytics": return self.send_html(analytics_page(user))
        if p.path=="/alerts": return self.send_html(alerts_page(user))
        if p.path=="/activity": return self.send_html(activity_page(user))
        if p.path=="/audit": return self.send_html(audit_page(user))
        if p.path=="/map": return self.send_html(map_page(user))
        if p.path=="/driver": return self.send_html(driver_page(user))
        if p.path=="/account": return self.send_html(account_page(user))
        if p.path=="/users": return self.send_html(users_page(user))
        if p.path=="/master-data": return self.send_html(master_data_page(user))
        if p.path=="/users/edit":
            if user["role"]!="Admin": return self.send_html(forbidden(user),403)
            q=parse_qs(p.query)
            try: ident=int(q.get("id",["0"])[0])
            except ValueError: ident=0
            return self.send_html(user_edit_page(user,ident))
        if p.path=="/master-data/edit":
            if user["role"]!="Admin": return self.send_html(forbidden(user),403)
            q=parse_qs(p.query); kind=q.get("kind",[""])[0]
            try: ident=int(q.get("id",["0"])[0])
            except ValueError: ident=0
            return self.send_html(master_data_edit_page(user,kind,ident))
        if p.path=="/new": return self.send_html(trip_form(None,user) if user["role"] in ("Admin","Dispatcher") else forbidden(user))
        if p.path=="/export":
            result=export_page(parse_qs(p.query),user)
            if isinstance(result,tuple):
                data,start,end=result; fn="truck_monitor_export"+(f"_{start}_to_{end}" if start and end else f"_from_{start}" if start else f"_until_{end}")+".csv"
                self.send_response(200); self.send_header("Content-Type","text/csv; charset=utf-8"); self.send_header("Content-Disposition",f'attachment; filename="{fn}"'); self.send_header("Content-Length",str(len(data))); self.headers_security(); self.end_headers(); self.wfile.write(data); return
            return self.send_html(result)
        if p.path=="/api/trips": return self.api_trips(user)
        if p.path=="/api/dashboard": return self.api_dashboard(user)
        if len(parts)>=2 and parts[0]=="trip" and parts[1].isdigit():
            ident=int(parts[1])
            with closing(db()) as con: row=get_trip(con,ident)
            if not row: return self.send_html(layout("Not found",'<div class=card>Trip not found.</div>',user),404)
            if not user_can_view_trip(user,row):
                return self.send_html(forbidden(user),403)
            if len(parts)==3 and parts[2]=="edit": return self.send_html(trip_form(row,user) if user_can_edit(user,row) else forbidden(user))
            if len(parts)==4 and parts[2]=="event" and parts[3] in TIME_KEYS:
                return self.send_html(layout("Method not allowed",'<div class="error">Milestones must be recorded with the secure action button.</div>',user),405)
            return self.send_html(detail(row,user))
        return self.send_html(layout("Not found",'<div class=card>Page not found.</div>',user),404)

    def do_POST(self):
        p=urlparse(self.path); parts=p.path.strip("/").split("/")
        if p.path=="/login":
            try: _,form=self.read_form()
            except ValueError as e: return self.send_html(login_page(str(e)),400)
            username=normalize_text(form.get("username",[""])[0],100); password=form.get("password",[""])[0]
            if not login_allowed(username):
                return self.send_html(login_page("Too many failed attempts. Please wait a few minutes and try again."),429)
            with closing(db()) as con:
                row=con.execute("SELECT * FROM users WHERE username=? AND active=1",(username,)).fetchone()
                if not row or not verify_password(password,row["password_hash"]):
                    note_login_failure(username)
                    return self.send_html(login_page("Invalid username or password."),401)
                clear_login_failures(username)
                token=create_session(con,username); con.commit()
            return self.redirect("/",token)
        user=self.require_user()
        if not user: return
        try: item,form=self.read_form()
        except ValueError as e: return self.send_html(layout("Invalid request",f'<div class=error>{escape(str(e))}</div>',user),400)
        if not require_csrf(form,user): return self.send_html(layout("Forbidden",'<div class=error>Invalid security token. Refresh and try again.</div>',user),403)

        if p.path=="/logout":
            cookie=self.headers.get("Cookie",""); token=""
            for part in cookie.split(";"):
                if part.strip().startswith("session="): token=part.strip().split("=",1)[1]
            if token:
                with closing(db()) as con:
                    con.execute("DELETE FROM sessions WHERE token_hash=?",(hashlib.sha256(token.encode()).hexdigest(),)); con.commit()
            return self.redirect("/login")

        if user["role"]=="Viewer":
            return self.send_html(forbidden(user),403)

        if len(parts)==3 and parts[0]=="trip" and parts[1].isdigit() and parts[2]=="event":
            ident=int(parts[1])
            milestone=normalize_text(form.get("milestone",[""])[0],80)
            if milestone not in TIME_KEYS:
                return self.send_html(layout("Invalid milestone",'<div class="error">Please select a valid milestone.</div>',user),400)
            with closing(db()) as con:
                row=get_trip(con,ident)
            if not row: return self.send_html(layout("Not found",'<div class="card">Trip not found.</div>',user),404)
            if not user_can_edit(user,row): return self.send_html(forbidden(user),403)
            if row.get(milestone):
                return self.send_html(layout("Already recorded",'<div class="error">That milestone has already been recorded.</div>',user),400)
            with closing(db()) as con:
                try:
                    con.execute("BEGIN")
                    locked=get_trip(con,ident)
                    if not locked:
                        con.rollback(); return self.send_html(layout("Not found",'<div class="error">Trip not found.</div>',user),404)
                    if not user_can_edit(user,locked):
                        con.rollback(); return self.send_html(forbidden(user),403)
                    if locked.get(milestone):
                        con.rollback(); return self.send_html(layout("Already recorded",'<div class="error">That milestone has already been recorded.</div>',user),400)
                    stamp=now_iso()
                    cur=con.execute(f"UPDATE trips SET {milestone}=?,updated_at=?,updated_by=? WHERE id=? AND COALESCE({milestone},'')=''",(stamp,stamp,user["username"],ident))
                    if cur.rowcount != 1:
                        con.rollback(); return self.send_html(layout("Already recorded",'<div class="error">That milestone has already been recorded.</div>',user),400)
                    log_activity(con,ident,"Milestone recorded",TIME_LABELS[milestone],user["username"])
                    con.commit()
                except DBIntegrityError as e:
                    con.rollback()
                    return self.send_html(layout("Invalid milestone",f'<div class="error">{escape(str(e))}</div>',user),400)
            return_to=normalize_text(form.get("return_to",[""])[0],500)
            if return_to == "/" or (return_to.startswith("/?") and not return_to.startswith("//")):
                return self.redirect(return_to)
            return self.redirect(f"/trip/{ident}")

        if len(parts)==4 and parts[0]=="trip" and parts[1].isdigit() and parts[2]=="event" and parts[3] in TIME_KEYS:
            ident=int(parts[1])
            with closing(db()) as con:
                try:
                    con.execute("BEGIN")
                    row=get_trip(con,ident)
                    if not row: con.rollback(); return self.send_html(layout("Not found",'<div class="card">Trip not found.</div>',user),404)
                    if not user_can_edit(user,row): con.rollback(); return self.send_html(forbidden(user),403)
                    milestone=parts[3]
                    if row.get(milestone):
                        con.rollback(); return self.send_html(layout("Already recorded",'<div class="error">That milestone has already been recorded.</div>',user),400)
                    stamp=now_iso()
                    cur=con.execute(f"UPDATE trips SET {milestone}=?,updated_at=?,updated_by=? WHERE id=? AND COALESCE({milestone},'')=''",(stamp,stamp,user["username"],ident))
                    if cur.rowcount != 1:
                        con.rollback(); return self.send_html(layout("Already recorded",'<div class="error">That milestone has already been recorded.</div>',user),400)
                    log_activity(con,ident,"Milestone recorded",TIME_LABELS[milestone],user["username"])
                    con.commit()
                except DBIntegrityError as e:
                    con.rollback()
                    return self.send_html(layout("Invalid milestone",f'<div class="error">{escape(str(e))}</div>',user),400)
            return_to = normalize_text(form.get("return_to", [""])[0], 500)
            if return_to == "/" or (return_to.startswith("/?") and not return_to.startswith("//")):
                return self.redirect(return_to)
            return self.redirect(f"/trip/{ident}")

        if p.path=="/account":
            if normalize_text(form.get("action",[""])[0],20)!="password":
                return self.send_html(account_page(user,error="Invalid account action."),400)
            current=form.get("current_password",[""])[0]
            new_password=form.get("new_password",[""])[0]
            confirm=form.get("confirm_password",[""])[0]
            if not current or not new_password or not confirm:
                return self.send_html(account_page(user,error="All password fields are required."),400)
            if len(new_password)<10:
                return self.send_html(account_page(user,error="New password must be at least 10 characters."),400)
            if new_password!=confirm:
                return self.send_html(account_page(user,error="New passwords do not match."),400)
            with closing(db()) as con:
                row=con.execute("SELECT password_hash FROM users WHERE username=? AND active=1",(user["username"],)).fetchone()
                if not row or not verify_password(current,row["password_hash"]):
                    return self.send_html(account_page(user,error="Current password is incorrect."),400)
                con.execute("UPDATE users SET password_hash=? WHERE username=?",(hash_password(new_password),user["username"]))
                con.execute("DELETE FROM sessions WHERE username=?",(user["username"],))
                con.commit()
            return self.send_html(account_page(user,notice="Password updated successfully."))

        if p.path=="/users":
            if user["role"]!="Admin": return self.send_html(forbidden(user),403)
            action=normalize_text(form.get("action",["create"])[0],20)
            if action=="delete":
                try: ident=int(form.get("id",["0"])[0])
                except ValueError: return self.send_html(users_page(user,"Invalid user."),400)
                with closing(db()) as con:
                    target=con.execute("SELECT * FROM users WHERE id=?",(ident,)).fetchone()
                    if not target: return self.send_html(users_page(user,"User not found."),404)
                    if target["username"]==user["username"]: return self.send_html(users_page(user,"You cannot delete your current account."),400)
                    if target["role"]=="Admin" and con.execute("SELECT COUNT(*) n FROM users WHERE role='Admin' AND active=1").fetchone()["n"]<=1:
                        return self.send_html(users_page(user,"The last active Admin cannot be deleted."),400)
                    con.execute("DELETE FROM sessions WHERE username=?",(target["username"],))
                    con.execute("UPDATE trips SET assigned_user=NULL WHERE assigned_user=?",(target["username"],))
                    con.execute("DELETE FROM users WHERE id=?",(ident,)); con.commit()
                return self.redirect("/users")
            if action=="edit":
                try: ident=int(form.get("id",["0"])[0])
                except ValueError: return self.send_html(users_page(user,"Invalid user."),400)
                username=normalize_text(form.get("username",[""])[0],100); password=form.get("password",[""])[0]
                role=normalize_text(form.get("role",[""])[0],30); driver_name=normalize_text(form.get("driver_name",[""])[0],200); client_name=normalize_text(form.get("client_name",[""])[0],200); active=1 if form.get("active",["1"])[0]=="1" else 0
                if not username or role not in ROLES: return self.send_html(user_edit_page(user,ident,"Username and role are required."),400)
                if role=="Viewer" and not client_name: return self.send_html(user_edit_page(user,ident,"A Consignee / Client is required for a Viewer."),400)
                if role!="Viewer": client_name=""
                if password and len(password)<10: return self.send_html(user_edit_page(user,ident,"New password must be at least 10 characters."),400)
                with closing(db()) as con:
                    old=con.execute("SELECT * FROM users WHERE id=?",(ident,)).fetchone()
                    if not old: return self.send_html(users_page(user,"User not found."),404)
                    if old["username"]==user["username"] and not active: return self.send_html(user_edit_page(user,ident,"You cannot disable your current account."),400)
                    if old["role"]=="Admin" and not active and con.execute("SELECT COUNT(*) n FROM users WHERE role='Admin' AND active=1").fetchone()["n"]<=1:
                        return self.send_html(user_edit_page(user,ident,"The last active Admin cannot be disabled."),400)
                    if role=="Viewer" and not con.execute("SELECT 1 FROM clients WHERE active=1 AND lower(name)=lower(?)",(client_name,)).fetchone():
                        return self.send_html(user_edit_page(user,ident,"Selected client is not available."),400)
                    try:
                        if password: con.execute("UPDATE users SET username=?,password_hash=?,role=?,driver_name=?,client_name=?,active=? WHERE id=?",(username,hash_password(password),role,driver_name,client_name,active,ident))
                        else: con.execute("UPDATE users SET username=?,role=?,driver_name=?,client_name=?,active=? WHERE id=?",(username,role,driver_name,client_name,active,ident))
                        if old["username"]!=username:
                            con.execute("UPDATE trips SET assigned_user=? WHERE assigned_user=?",(username,old["username"]))
                            con.execute("DELETE FROM sessions WHERE username=?",(old["username"],))
                        elif password or not active:
                            con.execute("DELETE FROM sessions WHERE username=?",(username,))
                        con.commit()
                    except DBIntegrityError: return self.send_html(user_edit_page(user,ident,"Username already exists."),400)
                return self.redirect("/users")
                    
            username=normalize_text(form.get("username",[""])[0],100); password=form.get("password",[""])[0]; role=normalize_text(form.get("role",[""])[0],30); driver_name=normalize_text(form.get("driver_name",[""])[0],200); client_name=normalize_text(form.get("client_name",[""])[0],200)
            if role!="Viewer": client_name=""
            if not username or len(password)<10 or role not in ROLES: return self.send_html(users_page(user)+"<div class=error>Username, role and a 10+ character password are required.</div>",400)
            if role=="Viewer" and not client_name:
                return self.send_html(users_page(user)+'<div class="error">A Consignee / Client is required for a Viewer account.</div>',400)
            with closing(db()) as con:
                if role=="Viewer" and not con.execute("SELECT 1 FROM clients WHERE active=1 AND lower(name)=lower(?)",(client_name,)).fetchone():
                    return self.send_html(users_page(user)+'<div class="error">Selected Consignee / Client is not available.</div>',400)
                try:
                    con.execute("INSERT INTO users(username,password_hash,role,driver_name,client_name,created_at) VALUES(?,?,?,?,?,?)",(username,hash_password(password),role,driver_name,client_name,now_iso())); con.commit()
                except DBIntegrityError as e: return self.send_html(users_page(user)+f'<div class=error>{escape(str(e))}</div>',400)
            return self.redirect("/users")

        if p.path=="/master-data":
            if user["role"]!="Admin": return self.send_html(forbidden(user),403)
            action=normalize_text(form.get("action",["create"])[0],20); kind=normalize_text(form.get("kind",[""])[0],20); table={"trucker":"truckers","client":"clients"}.get(kind)
            if not table: return self.send_html(master_data_page(user,"Invalid master-data type."),400)
            if action=="delete":
                try: ident=int(form.get("id",["0"])[0])
                except ValueError: return self.send_html(master_data_page(user,"Invalid record."),400)
                with closing(db()) as con:
                    r=con.execute(f"SELECT name FROM {table} WHERE id=?",(ident,)).fetchone()
                    if not r: return self.send_html(master_data_page(user,"Record not found."),404)
                    name=r["name"]
                    trips=con.execute("SELECT COUNT(*) n FROM trips WHERE lower(COALESCE(trucker_name,''))=lower(?)",(name,)).fetchone()["n"] if kind=="trucker" else con.execute("SELECT COUNT(*) n FROM trips WHERE lower(COALESCE(client,''))=lower(?)",(name,)).fetchone()["n"]
                    viewers=con.execute("SELECT COUNT(*) n FROM users WHERE role='Viewer' AND lower(COALESCE(client_name,''))=lower(?)",(name,)).fetchone()["n"] if kind=="client" else 0
                    if trips+viewers: return self.send_html(master_data_page(user,f'Cannot delete "{name}" because it is still in use.'),400)
                    con.execute(f"DELETE FROM {table} WHERE id=?",(ident,)); con.commit()
                return self.redirect("/master-data")
            if action=="edit":
                try: ident=int(form.get("id",["0"])[0])
                except ValueError: return self.send_html(master_data_page(user,"Invalid record."),400)
                name=normalize_text(form.get("name",[""])[0],200); active=1 if form.get("active",["1"])[0]=="1" else 0
                if not name: return self.send_html(master_data_edit_page(user,kind,ident,"Name is required."),400)
                with closing(db()) as con:
                    old=con.execute(f"SELECT name FROM {table} WHERE id=?",(ident,)).fetchone()
                    if not old: return self.send_html(master_data_page(user,"Record not found."),404)
                    try:
                        con.execute(f"UPDATE {table} SET name=?,active=? WHERE id=?",(name,active,ident))
                        if old["name"].lower()!=name.lower():
                            if kind=="trucker": con.execute("UPDATE trips SET trucker_name=? WHERE lower(COALESCE(trucker_name,''))=lower(?)",(name,old["name"]))
                            else:
                                con.execute("UPDATE trips SET client=? WHERE lower(COALESCE(client,''))=lower(?)",(name,old["name"]))
                                con.execute("UPDATE users SET client_name=? WHERE role='Viewer' AND lower(COALESCE(client_name,''))=lower(?)",(name,old["name"]))
                        con.commit()
                    except DBIntegrityError: return self.send_html(master_data_edit_page(user,kind,ident,"That name already exists."),400)
                return self.redirect("/master-data")
            name=normalize_text(form.get("name",[""])[0],200)
            if not name: return self.send_html(master_data_page(user,"Please provide a valid name."),400)
            with closing(db()) as con:
                try: con.execute(f"INSERT INTO {table}(name,created_at,created_by) VALUES(?,?,?)",(name,now_iso(),user["username"])); con.commit()
                except DBIntegrityError: return self.send_html(master_data_page(user,"That name already exists."),400)
            return self.redirect("/master-data")

        if p.path=="/new" or (len(parts)==3 and parts[0]=="trip" and parts[1].isdigit() and parts[2]=="edit"):
            if user["role"] not in ("Admin","Dispatcher") and not (user["role"]=="Driver" and len(parts)==3): return self.send_html(forbidden(user),403)
            item=normalize_record(item); item["container_no"]=normalize_text(item.get("container_no"),100); item["driver_name"]=normalize_text(item.get("driver_name"),200); item["contact_no"]=normalize_text(item.get("contact_no"),80)
            if user["role"]=="Driver": item["assigned_user"]=user["username"]
            item["status"] = "On Hold" if item.get("status")=="On Hold" else effective_status(item)
            errors=validate_trip(item)
            if errors:
                return self.send_html(trip_form(item,user,"\n".join(errors)),400)
            now=now_iso()
            columns=["container_no","driver_name","trucker_name","contact_no","status","priority","current_location","court_yard_name","cargo_type","shipping_line","client","latitude","longitude","last_location_at","assigned_user",*TIME_KEYS,"tags","notes"]
            values=[item.get(c) if c not in TIME_KEYS else item.get(c) for c in columns]
            try:
                with closing(db()) as con:
                    con.execute("BEGIN")
                    if p.path=="/new":
                        con.execute(f"INSERT INTO trips ({','.join(columns)},created_at,updated_at,created_by,updated_by) VALUES ({','.join('?'*len(columns))},?,?,?,?)",values+[now,now,user["username"],user["username"]])
                        ident=con.execute("SELECT id FROM trips WHERE container_no=?",(item["container_no"],)).fetchone()["id"]
                        log_activity(con,ident,"Trip created",f"Container {item['container_no']} registered",user["username"])
                    else:
                        ident=int(parts[1]); old=get_trip(con,ident)
                        if not old: con.rollback(); return self.send_html(layout("Not found",'<div class=card>Trip not found.</div>',user),404)
                        if not user_can_edit(user,old): con.rollback(); return self.send_html(forbidden(user),403)
                        immutable_errors=validate_milestone_update(old,item)
                        if immutable_errors:
                            con.rollback(); return self.send_html(trip_form(item,user,"\n".join(immutable_errors)),400)
                        if user["role"]=="Driver":
                            item["assigned_user"]=user["username"]
                        set_sql=','.join(c+'=?' for c in columns)
                        con.execute(f"UPDATE trips SET {set_sql},updated_at=?,updated_by=? WHERE id=?",values+[now,user["username"],ident])
                        log_activity(con,ident,"Trip updated","Trip details changed",user["username"])
                    con.commit()
                return self.redirect(f"/trip/{ident}")
            except DBIntegrityError as e:
                return self.send_html(trip_form(item,user,f"Database error: {e}"),400)
            except Exception:
                raise
        return self.send_html(layout("Not found",'<div class=card>Page not found.</div>',user),404)

    def api_trips(self,user):
        with closing(db()) as con:
            rows = visible_trips(con, user)
        for r in rows:
            r["display_status"] = effective_status(r)
        return self.json_response({"trips":rows,"server_time":now_iso()})

    def api_dashboard(self,user):
        with closing(db()) as con: rows,_,counts=dashboard_data(con,user=user)
        return self.json_response({"counts":counts,"total":len(rows),"server_time":now_iso()})

    def json_response(self,obj,code=200):
        data=json.dumps(obj,default=str).encode(); self.send_response(code); self.send_header("Content-Type","application/json"); self.send_header("Content-Length",str(len(data))); self.send_header("Cache-Control","no-store"); self.headers_security(); self.end_headers(); self.wfile.write(data)

    def log_message(self,*args): pass


class _WSGIHTTPServerStub:
    server_name = "localhost"
    server_port = PORT


def _wsgi_call_handler(environ):
    path = environ.get("PATH_INFO", "/") or "/"
    query = environ.get("QUERY_STRING", "")
    target = path + (("?" + query) if query else "")
    method = environ.get("REQUEST_METHOD", "GET").upper()
    body = b""
    length = environ.get("CONTENT_LENGTH", "")
    if length:
        try:
            size = int(length)
        except ValueError:
            size = 0
        if size < 0 or size > MAX_REQUEST_BYTES:
            raise ValueError("Request too large.")
        body = environ["wsgi.input"].read(size)

    headers = []
    host = environ.get("HTTP_HOST")
    if host:
        headers.append(("Host", host))
    else:
        headers.append(("Host", "localhost"))
    content_type = environ.get("CONTENT_TYPE")
    if content_type:
        headers.append(("Content-Type", content_type))
    if body:
        headers.append(("Content-Length", str(len(body))))
    cookie = environ.get("HTTP_COOKIE")
    if cookie:
        headers.append(("Cookie", cookie))
    user_agent = environ.get("HTTP_USER_AGENT")
    if user_agent:
        headers.append(("User-Agent", user_agent))
    accept = environ.get("HTTP_ACCEPT")
    if accept:
        headers.append(("Accept", accept))

    request = (
        f"{method} {target} HTTP/1.1\r\n"
        + "".join(f"{k}: {v}\r\n" for k, v in headers)
        + "Connection: close\r\n\r\n"
    ).encode("latin-1") + body

    import socket
    import threading

    client, server = socket.socketpair()
    client.settimeout(30)
    server.settimeout(30)

    def serve():
        try:
            Handler(server, ("127.0.0.1", 0), _WSGIHTTPServerStub())
        finally:
            try:
                server.close()
            except OSError:
                pass

    worker = threading.Thread(target=serve, daemon=True)
    worker.start()
    client.sendall(request)
    chunks = []
    while True:
        try:
            chunk = client.recv(65536)
        except socket.timeout:
            break
        if not chunk:
            break
        chunks.append(chunk)
    client.close()
    worker.join(timeout=5)

    raw = b"".join(chunks)
    header_end = raw.find(b"\r\n\r\n")
    if header_end < 0:
        raise RuntimeError("Invalid HTTP response from application handler.")
    head = raw[:header_end].decode("iso-8859-1")
    response_body = raw[header_end + 4:]
    lines = head.split("\r\n")
    status_line = lines[0].split(" ", 2)
    status = status_line[1] if len(status_line) >= 2 else "500"
    reason = status_line[2] if len(status_line) >= 3 else ""
    response_headers = []
    for line in lines[1:]:
        if not line or ":" not in line:
            continue
        key, value = line.split(":", 1)
        response_headers.append((key.strip(), value.lstrip()))
    return f"{status} {reason}".strip(), response_headers, response_body


def app(environ, start_response):
    initialize()
    try:
        status, headers, body = _wsgi_call_handler(environ)
    except ValueError as exc:
        body = str(exc).encode("utf-8")
        status = "413 Request Entity Too Large"
        headers = [
            ("Content-Type", "text/plain; charset=utf-8"),
            ("Content-Length", str(len(body))),
            ("Cache-Control", "no-store"),
        ]
    except Exception as exc:
        print(f"WSGI error: {type(exc).__name__}: {exc}", flush=True)
        body = b"Internal Server Error"
        status = "500 Internal Server Error"
        headers = [
            ("Content-Type", "text/plain; charset=utf-8"),
            ("Content-Length", str(len(body))),
            ("Cache-Control", "no-store"),
        ]
    existing = {k.lower() for k, _ in headers}
    if "content-length" not in existing:
        headers.append(("Content-Length", str(len(body))))
    headers.extend(security_wsgi())
    start_response(status, headers)
    return [body]


def security_wsgi():
    return [("X-Content-Type-Options","nosniff"),("X-Frame-Options","SAMEORIGIN"),("Referrer-Policy","strict-origin-when-cross-origin")]


if __name__=="__main__":
    initialize()

    server = None
    selected_port = PORT
    for candidate_port in range(PORT, PORT + 20):
        try:
            server = ThreadingHTTPServer(("0.0.0.0", candidate_port), Handler)
            selected_port = candidate_port
            break
        except OSError:
            continue

    if server is None:
        raise OSError(f"No available port found from {PORT} to {PORT + 19}.")

    PORT = selected_port
    print(f"Truck Monitor running on http://127.0.0.1:{PORT}")
    server.serve_forever()
