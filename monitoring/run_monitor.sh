#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BACKEND_DIR="${ROOT_DIR}/monitoring/backend"
FRONTEND_DIR="${ROOT_DIR}/monitoring/frontend"

if ! command -v npm >/dev/null 2>&1; then
  echo "ERROR: npm not found. Install Node.js/npm first." >&2
  exit 1
fi

if [ ! -d "${FRONTEND_DIR}/node_modules" ] || [ ! -x "${FRONTEND_DIR}/node_modules/.bin/vite" ]; then
  echo "Installing frontend dependencies (first run)..."
  (
    cd "${FRONTEND_DIR}"
    npm install
  )
fi

echo "Starting Flask backend on http://127.0.0.1:5001"
(
  cd "${BACKEND_DIR}"
  python3 app.py
) &
BACK_PID=$!

echo "Starting Svelte dev server on http://127.0.0.1:5174"
(
  cd "${FRONTEND_DIR}"
  npm run dev
) &
FRONT_PID=$!

echo "Monitor UI: http://127.0.0.1:5174"
echo "API only:   http://127.0.0.1:5001/api/snapshot"

cleanup() {
  kill "${BACK_PID}" "${FRONT_PID}" >/dev/null 2>&1 || true
}
trap cleanup EXIT INT TERM

wait "${BACK_PID}" "${FRONT_PID}"
