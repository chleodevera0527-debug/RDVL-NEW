import os
import sqlite3
import sys
from datetime import datetime

if len(sys.argv) != 2:
    raise SystemExit("Usage: python migrate_sqlite_to_postgres.py path/to/truck_monitor.db")

sqlite_path = sys.argv[1]
if not os.getenv("DATABASE_URL", "").startswith(("postgres://", "postgresql://")):
    raise SystemExit("DATABASE_URL must point to the target PostgreSQL database.")

import app
app.initialize()

src = sqlite3.connect(sqlite_path)
src.row_factory = sqlite3.Row
with app.db() as dst:
    tables = ["trips", "activity_log", "users", "truckers", "clients", "sessions", "app_events"]
    for table in tables:
        rows = src.execute(f"SELECT * FROM {table}").fetchall()
        if not rows:
            continue
        cols = [d[0] for d in src.execute(f"SELECT * FROM {table} LIMIT 0").description]
        placeholders = ",".join("?" for _ in cols)
        col_sql = ",".join(cols)
        for row in rows:
            dst.execute(
                f"INSERT INTO {table} ({col_sql}) VALUES ({placeholders}) ON CONFLICT DO NOTHING",
                tuple(row[c] for c in cols),
            )
    for table in ["trips", "activity_log", "users", "truckers", "clients", "app_events"]:
        dst.execute(f"SELECT setval(pg_get_serial_sequence('{table}','id'), COALESCE((SELECT MAX(id) FROM {table}),1), true)")
    dst.commit()

src.close()
print(f"Migration completed: {datetime.now().isoformat(timespec='seconds')}")
