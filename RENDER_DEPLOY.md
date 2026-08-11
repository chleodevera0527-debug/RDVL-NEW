# R.DEVERA Truck Monitor — Render Production Deployment

## Architecture

Production uses **Render Web Service + Render Postgres**.

- SQLite remains available for local development when `DATABASE_URL` is absent.
- PostgreSQL is selected automatically when `DATABASE_URL` starts with `postgres://` or `postgresql://`.
- The web service can sleep/restart without losing business data because trips/users/logs live in Postgres.
- The app initializes/migrates the schema once per process, not on every request.

## Render setup

### Option A — use the included `render.yaml`

1. Commit these files:
   - `app.py`
   - `requirements.txt`
   - `render.yaml`
2. Create a Render Blueprint from the repository.
3. Keep the Web Service and Postgres in the **same Render region**.
4. Set a strong `ADMIN_PASSWORD` as a secret in the Render dashboard before first production login.
5. Keep `ALLOW_DEFAULT_ADMIN=0`.
6. Keep `COOKIE_SECURE=1`.

### Option B — existing Render Web Service

If you already have the web service, create a Render Postgres database in the same region and add its **internal** connection string as:

`DATABASE_URL`

Also add:

- `APP_SECRET` — long random secret
- `COOKIE_SECURE=1`
- `ALLOW_DEFAULT_ADMIN=0`
- `ADMIN_USERNAME=admin`
- `ADMIN_PASSWORD` — strong secret

Build command:

`pip install -r requirements.txt`

Start command:

`gunicorn app:app --bind 0.0.0.0:$PORT --workers 2 --threads 4 --timeout 120`

## Existing SQLite data

The supplied `truck_monitor.db` was empty of trips/clients/truckers, so there is no production trip history to migrate right now.

If you later have SQLite data to migrate, make a backup first and run:

`DATABASE_URL="<TARGET_POSTGRES_URL>" python migrate_sqlite_to_postgres.py truck_monitor.db`

The helper initializes the PostgreSQL schema, copies the application tables, preserves IDs, and resets PostgreSQL sequences.

## Why not keep SQLite on Render?

Do not use the web service's local `truck_monitor.db` as the production source of truth. A web-service filesystem is not the right durability boundary for this application. Postgres is the durable system of record; the web process is disposable.

## Sleep / cold start behavior

A sleeping web service may be slow on the first request after inactivity. That does **not** threaten committed database records because the data is stored in Postgres. The application reconnects to Postgres when the process wakes.

## Optional connection pooling

For the current small deployment, direct internal Postgres connections are sufficient. If you later scale workers/services and approach the database connection limit, enable Render's managed PgBouncer connection pooling and point `DATABASE_URL` at the pool URL.
