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
    nav = '<a href="/">Dashboard</a>'
    if user:
        if user["role"] != "Viewer":
            nav += ' <a href="/analytics">Analytics</a><a href="/alerts">Alerts</a><a href="/activity">Activity</a><a href="/map">Map</a><a href="/driver">Driver</a>'
            if user["role"] in ("Admin", "Dispatcher"):
                nav += ' <a href="/new">+ New Trip</a>'
            nav += ' <a href="/export">Export</a><a href="/audit">Audit</a>'
            if user["role"] == "Admin":
                nav += ' <a href="/users">Users</a><a href="/master-data">Master Data</a>'
        account_name = user.get("driver_name") or user["username"]
        initials = "".join(x[0] for x in str(account_name).split()[:2]).upper() or "U"
        account_client = user.get("client_name") or ("All accounts" if user["role"] == "Admin" else "No client assigned")
        viewer_line = " · " + escape(account_client) if user["role"] == "Viewer" else ""
        account_html = '<details class="account-menu"><summary><span class="account-avatar">' + escape(initials[:2]) + '</span><span class="account-summary"><b>' + escape(account_name) + '</b><small>' + escape(user["role"]) + viewer_line + '</small></span><span class="account-chevron">⌄</span></summary><div class="account-dropdown"><div class="account-card-head"><span class="account-avatar large">' + escape(initials[:2]) + '</span><div><strong>' + escape(account_name) + '</strong><span>@' + escape(user["username"]) + '</span></div></div><div class="account-meta"><span>ROLE</span><b>' + escape(user["role"]) + '</b><span>ACCESS</span><b>' + escape(account_client) + '</b></div><a href="/account" class="account-link">My Account</a><form method="post" action="/logout" class="account-logout"><input type="hidden" name="csrf" value="' + escape(session_csrf(user)) + '"><button class="linkbtn">Log out</button></form></div></details>'
        nav += account_html
    return f'''<!doctype html>
<html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{escape(title)} | R.DEVERA LOGISTICS SERVICES</title>

<style>
:root{{
  --bg:#f5f7fb;--surface:#fff;--surface-2:#f8fafc;--border:#e7ebf2;
  --text:#172033;--muted:#718096;--primary:#2563eb;--primary-dark:#1d4ed8;
  --success:#16a34a;--warning:#d97706;--danger:#dc2626;--shadow:0 8px 30px rgba(15,23,42,.06);
  --radius:14px;
}}
*{{box-sizing:border-box}}
html{{background:var(--bg)}}
body{{font:14px Inter,ui-sans-serif,system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;margin:0;background:var(--bg);color:var(--text)}}
body:before{{content:"";position:fixed;inset:0;pointer-events:none;background:linear-gradient(135deg,rgba(37,99,235,.035),transparent 40%);z-index:-1}}
a{{color:var(--primary);text-decoration:none}}
a:hover{{color:var(--primary-dark)}}
header{{
  position:sticky;top:0;z-index:100;background:rgba(255,255,255,.92);backdrop-filter:blur(14px);
  border-bottom:1px solid var(--border);padding:14px 28px;display:flex;align-items:center;justify-content:space-between;gap:18px
}}
header h1{{font-size:17px;margin:0;font-weight:800;letter-spacing:-.3px;color:#111827}}
.brand{{display:flex;align-items:center;min-width:180px}}
.brand-logo{{width:190px;height:72px;object-fit:contain;object-position:center;background:#fff;border-radius:10px}}
.header-right{{display:flex;align-items:center;justify-content:flex-end;gap:18px;min-width:0;flex:1}}
 .viewer-table th:nth-child(3),.viewer-table td:nth-child(3){{display:none!important}}
.milestone-form{{display:inline-flex;align-items:center;margin:0}}
.milestone-select{{height:36px;min-width:142px;max-width:205px;border:1px solid #dbe4f0;border-radius:9px;background:#f7faff;padding:0 30px 0 12px;font:inherit;font-size:12px;color:#243b5a;font-weight:750;outline:none;cursor:pointer}}
.milestone-select:hover{{background:#eef4ff;border-color:#cbd9ef}}
.milestone-select:focus{{border-color:var(--primary);box-shadow:0 0 0 3px rgba(37,99,235,.10)}}
.update-trip-select option{{background:#fff;color:#243b5a;font-weight:650}}
@media(max-width:700px){{.milestone-select{{max-width:100%;min-width:140px}}}}
.account-menu{{position:relative;display:block;margin-left:4px}}
.account-menu summary{{list-style:none;cursor:pointer;display:flex;align-items:center;gap:8px;padding:4px 7px;border:1px solid transparent;border-radius:11px}}
.account-menu summary::-webkit-details-marker{{display:none}}
.account-menu[open] summary{{background:#f8fafc;border-color:var(--border)}}
.account-avatar{{width:34px;height:34px;border-radius:50%;background:#eaf1ff;color:var(--primary);display:inline-flex;align-items:center;justify-content:center;font-size:11px;font-weight:850;flex:none}}
.account-avatar.large{{width:42px;height:42px;font-size:13px}}
.account-summary{{display:flex;flex-direction:column;align-items:flex-start;line-height:1.15;min-width:0}}
.account-summary b{{font-size:12px;color:#1f2937;max-width:180px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}}
.account-summary small{{font-size:10px;color:var(--muted);max-width:180px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;margin-top:2px}}
.account-chevron{{color:#64748b;font-size:14px;margin-left:2px}}
.account-dropdown{{position:absolute;right:0;top:calc(100% + 8px);width:260px;background:#fff;border:1px solid var(--border);border-radius:13px;padding:12px;box-shadow:0 16px 40px rgba(15,23,42,.14);z-index:300}}
.account-card-head{{display:flex;align-items:center;gap:10px;padding:4px 3px 11px;border-bottom:1px solid var(--border)}}
.account-card-head div{{display:flex;flex-direction:column;min-width:0}}
.account-card-head strong{{font-size:13px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}}
.account-card-head span{{font-size:10px;color:var(--muted);margin-top:2px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}}
.account-meta{{display:grid;grid-template-columns:70px 1fr;gap:5px 9px;padding:11px 3px;font-size:11px}}
.account-meta span{{color:#94a3b8;font-size:9px;font-weight:850;letter-spacing:.5px}}
.account-meta b{{color:#334155;font-weight:700;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}}
.account-link,.account-logout{{display:flex;width:100%;padding:9px 10px;border-radius:8px;font-weight:700;font-size:12px}}
.account-link:hover,.account-logout:hover{{background:#f1f5f9}}
.account-logout{{border:0;background:transparent;margin:0;text-align:left}}
.account-logout .linkbtn{{padding:0;background:transparent;color:#dc2626;font-size:12px;width:100%;justify-content:flex-start}}
nav{{display:flex;gap:6px;flex-wrap:wrap;align-items:center}}
nav a{{color:#475569;padding:8px 11px;border-radius:9px;font-weight:650}}
nav a:hover{{background:#eef4ff;color:var(--primary)}}
main{{max-width:1500px;margin:0 auto;padding:28px}}
h2{{font-size:24px;letter-spacing:-.6px;margin:0 0 18px}}
h3{{font-size:16px;margin:0 0 14px}}
.card{{background:var(--surface);border:1px solid var(--border);border-radius:var(--radius);padding:20px;box-shadow:var(--shadow);margin-bottom:18px}}
.toolbar{{display:flex;gap:10px;flex-wrap:wrap;align-items:end}}
input,select,textarea{{
  width:100%;border:1px solid #d8dee8;background:#fff;color:var(--text);border-radius:9px;
  padding:10px 12px;margin-top:6px;font:inherit;outline:none;transition:border-color .15s,box-shadow .15s
}}
input:focus,select:focus,textarea:focus{{border-color:#93b4f8;box-shadow:0 0 0 3px rgba(37,99,235,.10)}}
label{{display:block;font-weight:650;color:#334155}}
textarea{{min-height:90px;resize:vertical}}
button,.button{{
  background:var(--primary);color:#fff;border:0;border-radius:9px;padding:10px 15px;
  font-weight:750;cursor:pointer;display:inline-flex;align-items:center;justify-content:center;gap:7px
}}
button:hover,.button:hover{{background:var(--primary-dark);color:#fff}}
.button.secondary{{background:#eef2f7;color:#334155}}
.button.secondary:hover{{background:#e2e8f0}}
.danger{{background:var(--danger)}}
.grid{{display:grid;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));gap:14px}}
.wide{{grid-column:1/-1}}
table{{width:100%;border-collapse:separate;border-spacing:0;background:var(--surface);overflow:hidden}}
th,td{{padding:13px 12px;border-bottom:1px solid var(--border);text-align:left;vertical-align:top}}
th{{background:#f8fafc;font-size:10px;text-transform:uppercase;letter-spacing:.55px;color:#64748b;font-weight:800}}
tr:last-child td{{border-bottom:0}}
tbody tr:hover{{background:#fbfdff}}
.tag{{display:inline-flex;align-items:center;border-radius:999px;padding:4px 9px;background:#edf4ff;color:#1e4fae;font-size:10px;font-weight:800;margin:1px}}
.tag.auto{{background:#ecfdf3;color:#15803d}}
.status{{background:#fff7df;color:#8a5a00}}
.priority-normal{{background:#f1f5f9;color:#475569;border:1px solid #e2e8f0;margin-top:5px}}

.muted{{color:var(--muted);font-size:12px}}
.notice,.ok,.error,.issue{{padding:11px 13px;border-radius:9px;margin:10px 0;border:1px solid}}
.notice,.ok{{background:#ecfdf3;color:#166534;border-color:#bbf7d0}}
.error,.issue{{background:#fef2f2;color:#991b1b;border-color:#fecaca}}
.statgrid{{display:grid;grid-template-columns:repeat(auto-fit,minmax(165px,1fr));gap:13px;margin-bottom:18px}}
.stat{{
  display:block;background:var(--surface);border:1px solid var(--border);border-radius:13px;padding:17px;
  box-shadow:var(--shadow);transition:transform .15s,border-color .15s,box-shadow .15s
}}
.stat:hover{{transform:translateY(-2px);border-color:#c9d8f7;box-shadow:0 12px 30px rgba(15,23,42,.08)}}
.stat strong{{display:block;font-size:28px;line-height:1.1;margin-top:5px;letter-spacing:-.8px}}
.stat-link{{color:var(--text)}}
.stat-link:hover{{color:var(--text)}}
.stat-link.active{{outline:2px solid #93b4f8;background:#f3f7ff}}
.live{{display:flex;align-items:center;gap:7px;color:#15803d;font-size:12px;margin:0 0 14px;font-weight:650}}
.live:before{{content:"";width:7px;height:7px;border-radius:50%;background:#22c55e;box-shadow:0 0 0 4px #dcfce7}}
.actions-cell{{min-width:170px;width:170px}}
.action-buttons{{display:flex;gap:6px;align-items:center;flex-wrap:wrap}}
.action-btn{{display:inline-flex;align-items:center;justify-content:center;min-height:34px;padding:7px 11px;border-radius:8px;background:#eef4ff;color:#1d4ed8;border:1px solid #dbe7ff;font-size:12px;font-weight:750;white-space:nowrap}}
.action-btn:hover{{background:#e2ecff;color:#1d4ed8}}
.action-form{{margin:0}}
.action-update{{background:#f1f5f9;color:#475569;border-color:#e2e8f0;cursor:pointer}}
.action-update:hover{{background:#e2e8f0;color:#334155}}
.action-menu{{position:relative;display:inline-block;min-width:125px}}
.action-menu summary{{list-style:none;background:#eef4ff;color:#1d4ed8;border:1px solid #dbe7ff;border-radius:8px;padding:8px 11px;font-weight:750;cursor:pointer;white-space:nowrap;text-align:center}}
.action-menu summary::-webkit-details-marker{{display:none}}
.action-menu summary:hover{{background:#e2ecff}}
.action-menu-items{{position:absolute;right:0;top:calc(100% + 6px);z-index:50;min-width:185px;background:#fff;border:1px solid var(--border);border-radius:10px;box-shadow:0 14px 35px rgba(15,23,42,.13);overflow:hidden}}
.action-menu-items a{{display:block;padding:10px 13px;color:#334155;background:#fff}}
.action-menu-items a:hover{{background:#f5f8fc;color:var(--primary)}}
.master-data-actions{{margin-top:10px;display:flex;align-items:center;gap:8px}}
 .account-page-grid{{display:grid;grid-template-columns:minmax(280px,.75fr) minmax(360px,1.25fr);gap:14px;max-width:1050px;margin:0 auto}}
.account-profile-card{{padding:22px}}
.profile-hero{{display:flex;align-items:center;gap:13px;padding-bottom:18px;border-bottom:1px solid var(--border)}}
.profile-avatar{{width:56px;height:56px;font-size:17px}}
.profile-hero h2{{margin:0 0 3px;font-size:20px}}
.profile-hero p{{margin:0;color:var(--muted);font-size:11px}}
.profile-info{{display:grid;gap:13px;padding-top:18px}}
.profile-info div{{display:flex;flex-direction:column;gap:3px}}
.profile-info span{{font-size:9px;color:#94a3b8;font-weight:850;letter-spacing:.6px}}
.profile-info strong{{font-size:12px;color:#334155}}
@media(max-width:800px){{.account-page-grid{{grid-template-columns:1fr}}.account-summary{{display:none}}.account-dropdown{{width:245px}}}}
.admin-actions{{display:flex;gap:6px;align-items:center;flex-wrap:wrap}}
.admin-actions .button,.admin-actions button{{padding:7px 10px;font-size:12px}}
.admin-actions .danger{{background:#dc2626;color:#fff}}
.admin-actions .danger:hover{{background:#b91c1c}}

.master-data-actions button{{width:auto;min-width:125px;padding:9px 14px;white-space:nowrap}}
@media(max-width:600px){{.master-data-actions button{{width:100%}}}}
.dashboard-info-grid{{display:grid;grid-template-columns:minmax(210px,.55fr) minmax(320px,1.45fr);gap:10px;margin-bottom:12px}}
.info-card{{background:var(--surface);border:1px solid var(--border);border-radius:11px;padding:11px 14px;box-shadow:var(--shadow);min-height:82px}}
.info-card-top{{display:flex;justify-content:space-between;align-items:center;color:#64748b;font-size:9px;font-weight:850;letter-spacing:.55px}}
.info-icon{{font-size:18px;color:var(--primary)}}
.info-main{{font-size:15px;font-weight:800;margin-top:8px;letter-spacing:-.2px}}
.info-sub{{color:var(--muted);font-size:10px;margin-top:2px}}
.weather-main{{display:flex;align-items:center;gap:9px;margin-top:7px}}
.weather-icon{{font-size:28px;line-height:1}}
.weather-main strong{{font-size:22px;letter-spacing:-.7px}}
.weather-location{{max-width:170px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}}
.weather-details{{display:flex;gap:10px;flex-wrap:wrap;margin-top:7px;color:#64748b;font-size:10px}}
.weather-details b{{color:#334155}}.table-wrap{{overflow-x:auto;border:1px solid var(--border);border-radius:12px}}
.empty{{padding:35px;text-align:center;color:#94a3b8}}
.milestone{{display:grid;gap:6px;align-content:start}}
.time-button{{justify-self:start;background:#475569;padding:7px 10px;font-size:12px}}
.time-note{{color:var(--muted);font-size:12px;min-height:18px}}
@media(max-width:800px){{
  header{{padding:12px 16px;align-items:flex-start;flex-direction:column}}
  .brand-logo{{width:175px;height:60px}}
  .header-right{{width:100%;justify-content:space-between;align-items:center;flex-wrap:wrap}}
  .dashboard-info-grid{{grid-template-columns:1fr;gap:8px}}
  nav{{width:100%;overflow-x:auto;flex-wrap:nowrap}}
  main{{padding:18px 14px}}
  h2{{font-size:21px}}
  .statgrid{{grid-template-columns:repeat(2,minmax(0,1fr))}}
}}
@media(max-width:500px){{.statgrid{{grid-template-columns:1fr 1fr}}.card{{padding:15px}}}}

/* PREMIUM UI OVERRIDES */
:root{{
  --bg:#f3f6fb;--surface:#ffffff;--surface-2:#f7f9fc;--border:#e3e8f0;
  --text:#142033;--muted:#718096;--primary:#0b63f6;--primary-dark:#084dcc;
  --accent:#13b8a6;--success:#16a34a;--warning:#d97706;--danger:#dc2626;
  --shadow:0 10px 35px rgba(15,23,42,.07);--shadow-lg:0 20px 55px rgba(15,23,42,.11);
  --radius:16px;
}}
html{{scroll-behavior:smooth}}
body{{
  background:
    radial-gradient(circle at 8% 0%,rgba(11,99,246,.08),transparent 28rem),
    radial-gradient(circle at 92% 4%,rgba(19,184,166,.07),transparent 25rem),
    var(--bg);
  color:var(--text);
}}
header{{
  min-height:76px;padding:12px 30px;
  background:rgba(255,255,255,.86);
  backdrop-filter:blur(20px) saturate(150%);
  border-bottom:1px solid rgba(226,232,240,.9);
  box-shadow:0 5px 24px rgba(15,23,42,.045);
}}
.brand{{gap:12px}}
.brand:after{{
  content:"LOGISTICS CONTROL CENTER";
  display:block;color:#94a3b8;font-size:8px;font-weight:850;letter-spacing:1.35px;
  padding-left:3px;white-space:nowrap;
}}
.brand-logo{{
  width:168px;height:58px;background:transparent;border-radius:12px;
  filter:drop-shadow(0 5px 12px rgba(15,23,42,.08));
}}
.header-right{{gap:14px}}
nav{{
  gap:4px;padding:4px;background:#f7f9fc;border:1px solid #e7ebf2;
  border-radius:13px;
}}
nav a{{
  position:relative;color:#526176;padding:8px 10px;border-radius:9px;
  font-size:11px;font-weight:800;transition:.18s ease;
}}
nav a:hover{{
  background:#fff;color:var(--primary);box-shadow:0 4px 14px rgba(15,23,42,.07);
  transform:translateY(-1px);
}}
nav a[href="/new"]{{background:var(--primary);color:#fff;box-shadow:0 7px 18px rgba(11,99,246,.2)}}
nav a[href="/new"]:hover{{background:var(--primary-dark);color:#fff}}
main{{max-width:1540px;padding:30px}}
h2{{
  font-size:28px;line-height:1.15;font-weight:850;letter-spacing:-1px;
  color:#101a2c;margin-bottom:20px;
}}
h3{{font-size:16px;font-weight:850;color:#172033}}
.card{{
  border:1px solid rgba(226,232,240,.95);border-radius:16px;padding:21px;
  box-shadow:var(--shadow);transition:transform .18s ease,box-shadow .18s ease,border-color .18s ease;
}}
.card:hover{{border-color:#d5dfef;box-shadow:var(--shadow-lg)}}
.statgrid{{gap:14px}}
.stat{{
  position:relative;overflow:hidden;border-radius:16px;padding:19px;
  border:1px solid #e3e8f0;box-shadow:var(--shadow);
  background:linear-gradient(145deg,#fff 0%,#fbfdff 100%);
}}
.stat:before{{
  content:"";position:absolute;right:-32px;top:-38px;width:110px;height:110px;border-radius:50%;
  background:linear-gradient(135deg,rgba(11,99,246,.11),rgba(19,184,166,.04));
}}
.stat:after{{
  content:"";position:absolute;left:0;top:0;bottom:0;width:3px;background:linear-gradient(180deg,var(--primary),var(--accent));
  opacity:.9;
}}
.stat strong{{font-size:30px;font-weight:900;color:#111b2d}}
.stat .muted{{font-size:10px;font-weight:800;letter-spacing:.55px;text-transform:uppercase}}
.stat:hover{{transform:translateY(-3px);box-shadow:0 18px 42px rgba(15,23,42,.1)}}
.table-wrap{{
  overflow-x:auto;border:1px solid #e2e8f0;border-radius:15px;
  box-shadow:0 8px 25px rgba(15,23,42,.045);background:#fff;
}}
table{{background:#fff}}
th{{
  background:linear-gradient(180deg,#f9fbfd,#f4f7fb);color:#64748b;
  padding:12px;font-size:9px;letter-spacing:.8px;border-bottom:1px solid #e1e7ef;
}}
td{{padding:13px 12px;color:#334155;font-size:12px}}
tbody tr{{transition:background .14s ease}}
tbody tr:hover{{background:#f7fbff}}
.tag{{
  border:1px solid #d9e7ff;background:#eff5ff;color:#1754b5;
  padding:5px 9px;font-size:9px;letter-spacing:.1px;
}}
.tag.auto{{background:#ecfdf5;border-color:#c7f0dc;color:#087443}}
.status{{background:#fff8e6;border-color:#f7df9f;color:#8a5a00}}
.priority-normal{{background:#f5f7fa;border-color:#e3e8ef}}
button,.button{{
  border-radius:10px;padding:10px 15px;font-size:12px;
  box-shadow:0 6px 16px rgba(11,99,246,.13);transition:.17s ease;
}}
button:hover,.button:hover{{transform:translateY(-1px);box-shadow:0 9px 21px rgba(11,99,246,.18)}}
.button.secondary{{box-shadow:none;border:1px solid #e1e7ef;background:#f7f9fc}}
input,select,textarea{{
  border-radius:10px;border-color:#dbe2ec;background:#fbfcfe;
  transition:.17s ease;
}}
input:hover,select:hover,textarea:hover{{border-color:#c5d2e4;background:#fff}}
input:focus,select:focus,textarea:focus{{
  background:#fff;border-color:#77a7fa;box-shadow:0 0 0 4px rgba(11,99,246,.09);
}}
.live{{
  background:#ecfdf5;border:1px solid #c9f0dc;width:max-content;
  padding:6px 10px;border-radius:999px;color:#087443;font-size:10px;
}}
.live:before{{width:6px;height:6px;box-shadow:0 0 0 4px #d8f8e7}}
.notice,.ok,.error,.issue{{border-radius:11px;padding:12px 14px}}
.dashboard-info-grid{{gap:14px}}
.info-card{{
  border-radius:15px;padding:15px;box-shadow:var(--shadow);
  background:linear-gradient(145deg,#fff,#f9fbfd);
}}
.info-card-top{{font-size:9px}}
.info-icon{{width:30px;height:30px;display:inline-flex;align-items:center;justify-content:center;border-radius:9px;background:#eef5ff}}
.info-main{{font-size:17px}}
.weather-main strong{{font-size:24px}}
.account-menu summary{{padding:5px 8px}}
.account-menu[open] summary{{box-shadow:0 5px 18px rgba(15,23,42,.06)}}
.account-avatar{{
  background:linear-gradient(135deg,#eaf2ff,#dff8f4);color:#1453b8;
  border:1px solid #d8e5f5;box-shadow:0 4px 12px rgba(15,23,42,.07);
}}
.account-dropdown{{border-radius:15px;box-shadow:0 20px 50px rgba(15,23,42,.16)}}
.action-btn{{
  border-radius:9px;background:#f0f5ff;border-color:#dce8ff;
  transition:.16s ease;
}}
.action-btn:hover{{transform:translateY(-1px);box-shadow:0 5px 14px rgba(11,99,246,.09)}}
.milestone-select{{border-radius:10px;background:#f8fbff}}
.empty{{padding:50px 30px}}
@media(max-width:800px){{
  header{{padding:10px 14px}}
  .brand{{width:100%;justify-content:flex-start}}
  .brand:after{{display:none}}
  .brand-logo{{width:158px;height:54px}}
  nav{{max-width:100%;padding:3px}}
  nav a{{padding:8px 9px;font-size:10px}}
  main{{padding:18px 12px}}
  h2{{font-size:23px}}
}}
@media(max-width:500px){{
  .statgrid{{gap:9px}}.stat{{padding:14px}}.stat strong{{font-size:24px}}
  .card{{padding:14px}}
}}

</style>

{('<script>setTimeout(()=>location.reload(),5000)</script>' if refresh else '')}
</head><body><header>
<div class="brand"><img class="brand-logo" src="data:image/jpeg;base64,/9j/4AAQSkZJRgABAQAAkACQAAD/4QD2RXhpZgAATU0AKgAAAAgABwEOAAIAAAALAAAAYgESAAMAAAABAAEAAAEaAAUAAAABAAAAbgEbAAUAAAABAAAAdgEoAAMAAAABAAIAAAEyAAIAAAAUAAAAfodpAAQAAAABAAAAkgAAAABTY3JlZW5zaG90AAAAAACQAAAAAQAAAJAAAAABMjAyNjowMToyNiAxODo0MTozMAAABJADAAIAAAAUAAAAyJKGAAcAAAASAAAA3KACAAQAAAABAAAD86ADAAQAAAABAAADWgAAAAAyMDI2OjAxOjI2IDE4OjQxOjMwAEFTQ0lJAAAAU2NyZWVuc2hvdP/tADhQaG90b3Nob3AgMy4wADhCSU0EBAAAAAAAADhCSU0EJQAAAAAAENQdjNmPALIE6YAJmOz4Qn7/4gIoSUNDX1BST0ZJTEUAAQEAAAIYYXBwbAQAAABtbnRyUkdCIFhZWiAH5gABAAEAAAAAAABhY3NwQVBQTAAAAABBUFBMAAAAAAAAAAAAAAAAAAAAAAAA9tYAAQAAAADTLWFwcGwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAApkZXNjAAAA/AAAADBjcHJ0AAABLAAAAFB3dHB0AAABfAAAABRyWFlaAAABkAAAABRnWFlaAAABpAAAABRiWFlaAAABuAAAABRyVFJDAAABzAAAACBjaGFkAAAB7AAAACxiVFJDAAABzAAAACBnVFJDAAABzAAAACBtbHVjAAAAAAAAAAEAAAAMZW5VUwAAABQAAAAcAEQAaQBzAHAAbABhAHkAIABQADNtbHVjAAAAAAAAAAEAAAAMZW5VUwAAADQAAAAcAEMAbwBwAHkAcgBpAGcAaAB0ACAAQQBwAHAAbABlACAASQBuAGMALgAsACAAMgAwADIAMlhZWiAAAAAAAAD21QABAAAAANMsWFlaIAAAAAAAAIPfAAA9v////7tYWVogAAAAAAAASr8AALE3AAAKuVhZWiAAAAAAAAAoOAAAEQsAAMi5cGFyYQAAAAAAAwAAAAJmZgAA8qcAAA1ZAAAT0AAACltzZjMyAAAAAAABDEIAAAXe///zJgAAB5MAAP2Q///7ov///aMAAAPcAADAbv/AABEIA1oD8wMBIgACEQEDEQH/xAAfAAABBQEBAQEBAQAAAAAAAAAAAQIDBAUGBwgJCgv/xAC1EAACAQMDAgQDBQUEBAAAAX0BAgMABBEFEiExQQYTUWEHInEUMoGRoQgjQrHBFVLR8CQzYnKCCQoWFxgZGiUmJygpKjQ1Njc4OTpDREVGR0hJSlNUVVZXWFlaY2RlZmdoaWpzdHV2d3h5eoOEhYaHiImKkpOUlZaXmJmaoqOkpaanqKmqsrO0tba3uLm6wsPExcbHyMnK0tPU1dbX2Nna4eLj5OXm5+jp6vHy8/T19vf4+fr/xAAfAQADAQEBAQEBAQEBAAAAAAAAAQIDBAUGBwgJCgv/xAC1EQACAQIEBAMEBwUEBAABAncAAQIDEQQFITEGEkFRB2FxEyIygQgUQpGhscEJIzNS8BVictEKFiQ04SXxFxgZGiYnKCkqNTY3ODk6Q0RFRkdISUpTVFVWV1hZWmNkZWZnaGlqc3R1dnd4eXqCg4SFhoeIiYqSk5SVlpeYmZqio6Slpqeoqaqys7S1tre4ubrCw8TFxsfIycrS09TV1tfY2dri4+Tl5ufo6ery8/T19vf4+fr/2wBDAAICAgICAgMCAgMFAwMDBQYFBQUFBggGBgYGBggKCAgICAgICgoKCgoKCgoMDAwMDAwODg4ODg8PDw8PDw8PDw//2wBDAQICAgQEBAcEBAcQCwkLEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBAQEBD/3QAEAED/2gAMAwEAAhEDEQA/AP38ooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooA//Q/fyiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigD/9H9/KKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKAP/0v38ooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooA//T/fyiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACi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tq92+7CiiivYPhAooooAKKKKACiiigD/0v38ooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooA//T/fyiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigD/9T9/KKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKAP/2Q==" alt="R. Devera Logistics Services"></div>
<div class="header-right">
<nav>{nav}</nav>
</div>
</header><main>{body}</main><script>
(function(){{function c(){{const n=new Date(),d=document.getElementById("live-date"),t=document.getElementById("live-time");if(d)d.textContent=n.toLocaleDateString("en-PH",{{timeZone:"Asia/Manila",weekday:"short",month:"short",day:"numeric",year:"numeric"}});if(t)t.textContent=n.toLocaleTimeString("en-PH",{{timeZone:"Asia/Manila",hour:"2-digit",minute:"2-digit",second:"2-digit",hour12:true}});}}c();setInterval(c,1000);}})();
</script>
</body></html>'''

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
    q = query.get("q",[""])[0].strip(); status = query.get("status",[""])[0]
    if status not in STATUSES: status = ""
    with closing(db()) as con:
        rows, filtered, counts = dashboard_data(con,q,status,user)
    tiles = [("All trips",len(rows),"")] + [(s,counts.get(s,0),s) for s in STATUSES]
    stats = ''.join(f'<a class="stat" href="/?{urlencode({"q":q,"status":s}) if s else urlencode({"q":q})}"><span class="muted">{escape(label)}</span><strong>{n}</strong></a>' for label,n,s in tiles)
    is_viewer = user["role"] == "Viewer"
    trucker_header = "" if is_viewer else "<th>Trucker</th>"
    rows_html=[]
    for d in filtered:
        actions = f'<div class="action-buttons"><a class="action-btn" href="/trip/{d["id"]}">View</a>'
        can_edit = user["role"] in ("Admin","Dispatcher") or (user["role"]=="Driver" and (not d.get("assigned_user") or d.get("assigned_user")==user["username"]))
        if can_edit:
            actions += f'<a class="action-btn" href="/trip/{d["id"]}/edit">Edit</a>'
            pending_milestones = [(ek, elabel) for ek, elabel in TIMES if not d.get(ek)]
            if pending_milestones:
                return_to = "/?" + urlencode({"q": q, "status": status}) if (q or status) else "/"
                milestone_labels = [
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
                options = ''.join(
                    f'<option value="{escape(ek)}">{escape(label)}</option>'
                    for ek, label in milestone_labels
                    if not d.get(ek)
                )
                actions += f'<form method="post" action="/trip/{d["id"]}/event" class="inline milestone-form"><input type="hidden" name="csrf" value="{escape(session_csrf(user))}"><input type="hidden" name="return_to" value="{escape(return_to)}"><select name="milestone" class="milestone-select update-trip-select" aria-label="Update Trip" onchange="if(this.value)this.form.submit()"><option value="" selected>Update Trip ▾</option>{options}</select></form>'
        actions += '</div>'
        rows_html.append(f'''<tr data-trip-id="{d['id']}">
<td><strong>{escape(d['container_no'])}</strong><br><span class="muted">{escape(d.get('client') or 'No client')}</span></td>
<td>{escape(d['driver_name'])}</td>{"" if is_viewer else f"<td>{escape(d.get('trucker_name') or 'Not set')}</td>"}<td>{escape(d.get('shipping_line') or "Not set")}</td><td>{escape(d['contact_no'])}</td>
<td><span class="tag status">{escape(d['display_status'])}</span><br><span class="tag priority-normal">{escape(d.get('priority') or 'Normal')}</span></td>
<td>{escape(d.get('cargo_type') or 'Not set')}</td><td>{escape(d.get('court_yard_name') or 'Not set')}</td>
<td>{escape(d.get('current_location') or 'Not set')}<br><span class="small">{escape(str(d.get('latitude') or ''))} {escape(str(d.get('longitude') or ''))}</span></td>
<td>{escape(d.get('notes') or '—')}</td><td><strong>{escape(d['latest_label'])}</strong><br><span class="muted">{escape(fmt(d['latest_time']))}</span></td><td>{actions}</td></tr>''')
    body = (f'<div class="notice">{escape(notice)}</div>' if notice else '') + f'''
<div class="live">Live database view · refreshes every {LIVE_REFRESH_SECONDS} seconds</div>
<div class="dashboard-info-grid">
<div class="info-card">
<div class="info-card-top"><span>LOCAL DATE &amp; TIME</span><span class="info-icon">◷</span></div>
<div id="dashboard-date" class="info-main">Loading...</div>
<div id="dashboard-time" class="info-sub">--:--:--</div>
</div>
<div class="info-card weather-card">
<div class="info-card-top"><span>LIVE WEATHER</span><span class="weather-location" id="weather-location">Detecting location...</span></div>
<div class="weather-main"><span id="weather-icon" class="weather-icon">☁️</span><div><strong id="weather-temp">--°</strong><div id="weather-desc" class="info-sub">Loading forecast...</div></div></div>
<div class="weather-details"><span>💧 <b id="weather-rain">--%</b></span><span>💨 <b id="weather-wind">-- km/h</b></span><span>Feels <b id="weather-feels">--°</b></span></div>
</div>
</div>
<script>
(function(){{
const fallback={{lat:14.5995,lon:120.9842,name:"Manila"}};
const desc={{0:"Clear sky",1:"Mainly clear",2:"Partly cloudy",3:"Overcast",45:"Fog",48:"Rime fog",51:"Light drizzle",53:"Drizzle",55:"Heavy drizzle",56:"Freezing drizzle",57:"Freezing drizzle",61:"Light rain",63:"Rain",65:"Heavy rain",66:"Freezing rain",67:"Heavy freezing rain",71:"Light snow",73:"Snow",75:"Heavy snow",77:"Snow grains",80:"Light showers",81:"Showers",82:"Heavy showers",85:"Snow showers",86:"Heavy snow showers",95:"Thunderstorm",96:"Thunderstorm + hail",99:"Thunderstorm + hail"}};
function icon(c){{if(c===0)return"☀️";if([1,2].includes(c))return"🌤️";if([3,45,48].includes(c))return"☁️";if([51,53,55,56,57,61,63,65,66,67,80,81,82].includes(c))return"🌧️";if([71,73,75,77,85,86].includes(c))return"🌨️";if([95,96,99].includes(c))return"⛈️";return"🌤️";}}
function clock(){{const n=new Date(),d=document.getElementById("dashboard-date"),t=document.getElementById("dashboard-time");if(d)d.textContent=n.toLocaleDateString("en-PH",{{timeZone:"Asia/Manila",weekday:"long",year:"numeric",month:"long",day:"numeric"}});if(t)t.textContent=n.toLocaleTimeString("en-PH",{{timeZone:"Asia/Manila",hour:"2-digit",minute:"2-digit",second:"2-digit",hour12:true}});}}
async function weather(lat,lon,name){{try{{const u="https://api.open-meteo.com/v1/forecast?latitude="+lat+"&longitude="+lon+"&current=temperature_2m,apparent_temperature,precipitation_probability,weather_code,wind_speed_10m&timezone=auto";const r=await fetch(u,{{cache:"no-store"}});if(!r.ok)throw 0;const x=await r.json(),c=x.current||{{}};document.getElementById("weather-location").textContent=name||x.timezone||"Current location";document.getElementById("weather-icon").textContent=icon(c.weather_code);document.getElementById("weather-temp").textContent=Math.round(c.temperature_2m)+"°";document.getElementById("weather-desc").textContent=desc[c.weather_code]||"Current conditions";document.getElementById("weather-rain").textContent=(c.precipitation_probability??"--")+"%";document.getElementById("weather-wind").textContent=Math.round(c.wind_speed_10m??0)+" km/h";document.getElementById("weather-feels").textContent=Math.round(c.apparent_temperature??c.temperature_2m)+"°";}}catch(e){{document.getElementById("weather-location").textContent="Weather unavailable";document.getElementById("weather-desc").textContent="Refresh to retry";}}}}
clock();setInterval(clock,1000);
if(navigator.geolocation){{navigator.geolocation.getCurrentPosition(p=>weather(p.coords.latitude,p.coords.longitude,"Your location"),()=>weather(fallback.lat,fallback.lon,fallback.name),{{timeout:5000,maximumAge:600000}});}}else weather(fallback.lat,fallback.lon,fallback.name);
}})();
</script><div class="statgrid">{stats}</div>
<div class="card"><form method="get" class="toolbar"><label>Search<input name="q" value="{escape(q)}" placeholder="{("Container, driver, shipping line, client, location, notes" if is_viewer else "Container, driver, trucker, shipping line, client, location, notes")}"></label><button>Filter</button><a class="button" href="/">Clear</a></form></div>
<div class="card"><div class="table-wrap"><table class="dashboard-table {("viewer-table" if is_viewer else "")}"><tr><th>Container / Client</th><th>Driver</th>{trucker_header}<th>Shipping Line</th><th>Contact</th><th>Status</th><th>Cargo</th><th>Court Yard</th><th>Location</th><th>Notes</th><th>Latest Update</th><th>Actions</th></tr>{''.join(rows_html) or f'<tr><td colspan="{11 if is_viewer else 12}" class="muted">No trips found.</td></tr>'}</table></div></div>
<script>setTimeout(()=>location.reload(),{LIVE_REFRESH_SECONDS*1000});</script>'''
    return layout("Dashboard",body,user,refresh=False)


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
