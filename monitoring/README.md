# VerifiedJS Live Monitor (Flask + Svelte)

This dashboard reads `agent_logs/`, `.agent_locks/`, `.worktrees/`, and `TASKS.md` to show live supervisor/agent progress.

## 1) Backend (Flask)

```bash
cd monitoring/backend
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
python3 app.py
```

Backend endpoints:
- `GET /api/snapshot`
- `GET /api/stream` (SSE live updates every 2s)
- `GET /api/log/<name>?lines=220`

## 2) Frontend (Svelte + Vite)

```bash
cd monitoring/frontend
npm install
npm run dev
```

Open: `http://127.0.0.1:5174`

The Vite dev server proxies `/api/*` to Flask on `127.0.0.1:5001`.

## 3) One-command local run

```bash
./monitoring/run_monitor.sh
```

This starts both Flask and Svelte dev servers.
