#!/usr/bin/env python3
"""Flask backend for VerifiedJS agent monitoring dashboard.

Reads from the SQLite database at .agent_state/state.db to serve
task queue state, agent checkpoints, and derived metrics.
"""
from __future__ import annotations

import json
import os
import queue
import signal
import sqlite3
import subprocess
import sys
import threading
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List

from flask import Flask, Response, jsonify, request, send_from_directory

ROOT = Path(os.environ.get("VERIFIEDJS_ROOT", Path(__file__).resolve().parents[2]))
DB_PATH = ROOT / ".agent_state" / "state.db"
TASKS_FILE = ROOT / "TASKS.md"
PROGRESS_FILE = ROOT / "PROGRESS.md"
CHOREO_FILE = ROOT / "agents" / "verified_compiler_agents.py"
FRONTEND_DIR = ROOT / "monitoring" / "frontend"
FRONTEND_DIST = FRONTEND_DIR / "dist"

app = Flask(__name__, static_folder=str(FRONTEND_DIST), static_url_path="")

# ---------------------------------------------------------------------------
# DB helpers
# ---------------------------------------------------------------------------

def get_db() -> sqlite3.Connection:
    conn = sqlite3.connect(str(DB_PATH), timeout=5)
    conn.row_factory = sqlite3.Row
    return conn


def query_tasks() -> List[Dict[str, Any]]:
    """Return all rows from the tasks table."""
    try:
        conn = get_db()
        rows = conn.execute("SELECT id, type, payload, status, owner, result FROM tasks ORDER BY id").fetchall()
        conn.close()
        result = []
        for r in rows:
            payload = {}
            try:
                payload = json.loads(r["payload"]) if r["payload"] else {}
            except (json.JSONDecodeError, TypeError):
                pass
            task_result = None
            try:
                task_result = json.loads(r["result"]) if r["result"] else None
            except (json.JSONDecodeError, TypeError):
                task_result = r["result"]
            result.append({
                "id": r["id"],
                "type": r["type"],
                "payload": payload,
                "status": r["status"],
                "owner": r["owner"] or "",
                "result": task_result,
            })
        return result
    except Exception:
        return []


def query_checkpoints() -> List[Dict[str, Any]]:
    """Return all rows from the checkpoints table."""
    try:
        conn = get_db()
        rows = conn.execute("SELECT agent_id, handoff, state, history FROM checkpoints ORDER BY agent_id").fetchall()
        conn.close()
        result = []
        for r in rows:
            state = {}
            try:
                state = json.loads(r["state"]) if r["state"] else {}
            except (json.JSONDecodeError, TypeError):
                pass
            history = []
            try:
                history = json.loads(r["history"]) if r["history"] else []
            except (json.JSONDecodeError, TypeError):
                pass
            result.append({
                "agent_id": r["agent_id"],
                "handoff": r["handoff"] or "",
                "state": state,
                "history_len": len(history) if isinstance(history, list) else 0,
                "last_message": _extract_last_message(history),
            })
        return result
    except Exception:
        return []


def _extract_last_message(history: Any) -> str:
    """Get the last assistant message content from history, truncated."""
    if not isinstance(history, list) or not history:
        return ""
    for msg in reversed(history):
        if isinstance(msg, dict) and msg.get("role") == "assistant":
            content = msg.get("content", "")
            if isinstance(content, str):
                return content[:300]
            if isinstance(content, list):
                for block in reversed(content):
                    if isinstance(block, dict) and block.get("type") == "text":
                        return block.get("text", "")[:300]
    return ""


def task_stats(tasks: List[Dict]) -> Dict[str, Any]:
    """Compute summary stats from task list."""
    by_status: Dict[str, int] = {}
    by_type: Dict[str, int] = {}
    by_owner: Dict[str, int] = {}
    for t in tasks:
        by_status[t["status"]] = by_status.get(t["status"], 0) + 1
        by_type[t["type"]] = by_type.get(t["type"], 0) + 1
        if t["owner"]:
            by_owner[t["owner"]] = by_owner.get(t["owner"], 0) + 1
    return {
        "total": len(tasks),
        "by_status": by_status,
        "by_type": by_type,
        "by_owner": by_owner,
    }


def parse_tasks_md() -> Dict[str, Any]:
    """Parse TASKS.md for high-level project progress."""
    items: List[Dict[str, str]] = []
    current_section = "Uncategorized"
    if TASKS_FILE.exists():
        with TASKS_FILE.open("r", encoding="utf-8", errors="replace") as fh:
            for raw in fh:
                line = raw.rstrip("\n")
                if line.startswith("## "):
                    current_section = line[3:].strip()
                elif line.startswith("- [ ] ") or line.startswith("- [x] "):
                    done = line.startswith("- [x] ")
                    text = line[6:].strip()
                    items.append({
                        "section": current_section,
                        "done": done,
                        "text": text,
                    })
    sections: Dict[str, Dict] = {}
    for item in items:
        sec = item["section"]
        if sec not in sections:
            sections[sec] = {"section": sec, "total": 0, "done": 0}
        sections[sec]["total"] += 1
        if item["done"]:
            sections[sec]["done"] += 1
    return {
        "items": items,
        "sections": list(sections.values()),
        "total": len(items),
        "done": sum(1 for i in items if i["done"]),
    }


def extract_task_details(task: Dict) -> Dict[str, Any]:
    """Extract rich details from a task's result payload."""
    result = task.get("result")
    if not isinstance(result, dict):
        return {}
    details: Dict[str, Any] = {}
    # From PlanResult
    if "tasks" in result and isinstance(result["tasks"], list):
        details["planned_tasks"] = result["tasks"]
        details["rationale"] = result.get("rationale", "")
    # From ContextBundle
    if "task_id" in result and "lean_source" in result:
        details["context_task_id"] = result["task_id"]
        details["context_files"] = list(result.get("lean_source", {}).keys())
        details["guidance"] = result.get("guidance", "")
        details["existing_sorrys"] = result.get("existing_sorrys", [])
        details["proof_blockers"] = result.get("proof_blockers", "")
    # From SpecResult / ProofResult
    if "file_writes" in result:
        details["file_writes"] = [
            {"path": fw.get("path", ""), "action": fw.get("action", "")}
            for fw in result.get("file_writes", [])
        ]
    if "sorrys_resolved" in result:
        details["sorrys_resolved"] = result["sorrys_resolved"]
        details["sorrys_remaining"] = result.get("sorrys_remaining", 0)
    # From ReviewResult
    if "verdict" in result:
        details["verdict"] = result["verdict"]
        details["feedback"] = result.get("feedback", "")
    return details


def git_status_short() -> List[str]:
    try:
        out = subprocess.check_output(
            ["git", "-C", str(ROOT), "status", "--short", "--branch"],
            text=True, stderr=subprocess.DEVNULL,
        )
        return out.splitlines()
    except Exception:
        return []


def git_recent_commits(n: int = 8) -> List[Dict[str, str]]:
    try:
        out = subprocess.check_output(
            ["git", "-C", str(ROOT), "log", f"-{n}", "--oneline", "--no-decorate"],
            text=True, stderr=subprocess.DEVNULL,
        )
        commits = []
        for line in out.strip().splitlines():
            parts = line.split(" ", 1)
            commits.append({"hash": parts[0], "message": parts[1] if len(parts) > 1 else ""})
        return commits
    except Exception:
        return []


def iso(ts: float) -> str:
    return datetime.fromtimestamp(ts, tz=timezone.utc).isoformat()


def load_choreography_source() -> Dict[str, Any]:
    """Load the choreography function source with line-number mapping for each phase."""
    if not CHOREO_FILE.exists():
        return {"lines": [], "phases": [], "func_start": 0, "func_end": 0}
    with CHOREO_FILE.open("r", encoding="utf-8", errors="replace") as fh:
        all_lines = fh.readlines()

    # Find the function boundaries
    func_start = 0
    func_end = len(all_lines)
    in_func = False
    for i, line in enumerate(all_lines):
        if "def verified_compiler_development_loop(" in line:
            func_start = i + 1  # 1-indexed
            in_func = True
            continue
        if in_func and i > func_start + 10:
            stripped = line.rstrip()
            # End of function = next top-level def/class or separator comment at col 0
            if stripped and not stripped.startswith(" ") and not stripped.startswith("\t"):
                if stripped.startswith("def ") or stripped.startswith("class ") or stripped.startswith("# ---"):
                    func_end = i  # line before this
                    break

    # Phase-to-line mapping based on the actual source markers
    phases = [
        {"id": "plan", "label": "Phase 1: Planning", "marker": "Phase 1: Planning", "line": 0},
        {"id": "context", "label": "Phase 2: Context Assembly", "marker": "Phase 2: Context assembly", "line": 0},
        {"id": "execute", "label": "Phase 3: Parallel Execution", "marker": "Phase 3: Parallel execution", "line": 0},
        {"id": "adversarial", "label": "Phase 3.5: Adversarial Testing", "marker": "Phase 3.5: Adversarial testing", "line": 0},
        {"id": "review", "label": "Phase 4: Review + Revision", "marker": "Phase 4: Review", "line": 0},
        {"id": "memory", "label": "Phase 5: Memory Persistence", "marker": "Phase 5: Memory persistence", "line": 0},
        {"id": "continue", "label": "Phase 6: Continue Decision", "marker": "Phase 6: Continue decision", "line": 0},
    ]
    for i, line in enumerate(all_lines):
        for phase in phases:
            if phase["marker"] in line:
                phase["line"] = i + 1  # 1-indexed

    # Extract just the function lines for display
    func_lines = []
    for i in range(func_start - 1, min(func_end, len(all_lines))):
        func_lines.append({"num": i + 1, "text": all_lines[i].rstrip("\n")})

    return {
        "lines": func_lines,
        "phases": phases,
        "func_start": func_start,
        "func_end": func_end,
    }


def classify_task_phase(task: Dict) -> str:
    """Map a task to its choreography phase based on type and context.

    Task types from effectful:
    - Template calls get the template name as type (e.g. 'plan_next_sprint')
    - scatter calls get 'scatter-{step_id}' as type
    - fan_out calls get 'fan-{step_id}:g{group}' as type
    """
    ttype = task.get("type", "")
    owner = task.get("owner", "")

    # Direct template-name matches
    if ttype == "plan_next_sprint":
        return "plan"
    if ttype == "review_completed_work":
        return "review"
    if ttype == "decide_continue":
        return "continue"
    if ttype == "persist_findings":
        return "memory"

    # scatter = context assembly phase (scatter dispatches to context-supervisor)
    if ttype.startswith("scatter-"):
        return "context"

    # fan_out = parallel execution or adversarial (check owner for disambiguation)
    if ttype.startswith("fan-"):
        if owner in ("spec-challenger", "fuzzer", "soundness-auditor"):
            return "adversarial"
        return "execute"

    # Owner-based fallback
    if owner == "planner-supervisor":
        return "plan"
    if owner == "context-supervisor":
        return "context"
    if owner in ("spec-writer-1", "spec-writer-2", "test-writer", "prover-1", "prover-2"):
        return "execute"
    if owner in ("spec-challenger", "fuzzer", "soundness-auditor"):
        return "adversarial"
    if owner == "memory-keeper":
        return "memory"

    return "unknown"


def infer_active_phase(tasks: List[Dict]) -> str:
    """Infer which choreography phase is currently active from task states."""
    # Find the latest non-done task to determine current phase
    for t in reversed(tasks):
        if t["status"] in ("claimed", "pending"):
            phase = classify_task_phase(t)
            if phase != "unknown":
                return phase
    # If all done, check what the last completed task was
    for t in reversed(tasks):
        if t["status"] == "done":
            phase = classify_task_phase(t)
            if phase != "unknown":
                return phase
    return "plan"


def agent_phase_positions(tasks: List[Dict], checkpoints: List[Dict]) -> Dict[str, str]:
    """Map each agent to the choreography phase they're currently at."""
    agent_phases: Dict[str, str] = {}

    # From active tasks (claimed/pending)
    for t in tasks:
        if t["owner"] and t["status"] in ("claimed",):
            phase = classify_task_phase(t)
            if phase != "unknown":
                agent_phases[t["owner"]] = phase

    # From checkpoints with handoff text
    for cp in checkpoints:
        aid = cp["agent_id"]
        if aid in agent_phases:
            continue  # active task takes priority
        handoff = (cp.get("handoff") or "").lower()
        if not handoff:
            continue
        if "plan" in handoff:
            agent_phases[aid] = "plan"
        elif "context" in handoff or "assemble" in handoff:
            agent_phases[aid] = "context"
        elif any(kw in handoff for kw in ("spec", "test", "prov", "implement", "write")):
            agent_phases[aid] = "execute"
        elif any(kw in handoff for kw in ("challeng", "fuzz", "audit", "adversar")):
            agent_phases[aid] = "adversarial"
        elif "review" in handoff:
            agent_phases[aid] = "review"
        elif "memory" in handoff or "persist" in handoff:
            agent_phases[aid] = "memory"
        elif "continue" in handoff or "decide" in handoff:
            agent_phases[aid] = "continue"

    # From last completed tasks for agents not yet mapped
    for t in reversed(tasks):
        if t["owner"] and t["owner"] not in agent_phases and t["status"] == "done":
            phase = classify_task_phase(t)
            if phase != "unknown":
                agent_phases[t["owner"]] = phase

    return agent_phases


def build_snapshot() -> Dict[str, Any]:
    tasks = query_tasks()
    checkpoints = query_checkpoints()
    stats = task_stats(tasks)
    tasks_md = parse_tasks_md()
    choreo = load_choreography_source()

    # Enrich tasks with extracted details and phase classification
    for t in tasks:
        t["details"] = extract_task_details(t)
        t["phase"] = classify_task_phase(t)

    active_phase = infer_active_phase(tasks)
    agent_positions = agent_phase_positions(tasks, checkpoints)

    return {
        "timestamp": iso(time.time()),
        "db_path": str(DB_PATH),
        "tasks": tasks,
        "task_stats": stats,
        "checkpoints": checkpoints,
        "tasks_md": tasks_md,
        "choreography": choreo,
        "active_phase": active_phase,
        "agent_positions": agent_positions,
        "agent_process": agent_proc.status,
        "git": {
            "status": git_status_short(),
            "recent_commits": git_recent_commits(),
        },
    }


# ---------------------------------------------------------------------------
# Routes
# ---------------------------------------------------------------------------

@app.after_request
def add_cors(resp):
    resp.headers["Access-Control-Allow-Origin"] = "*"
    resp.headers["Access-Control-Allow-Headers"] = "Content-Type"
    return resp


@app.get("/")
def index():
    """Serve the Svelte frontend."""
    index_path = FRONTEND_DIST / "index.html"
    if index_path.exists():
        return send_from_directory(str(FRONTEND_DIST), "index.html")
    return jsonify({
        "service": "verifiedjs-agent-monitor",
        "note": "Frontend not built. Run with --build or build manually.",
        "endpoints": ["/api/health", "/api/snapshot", "/api/stream",
                      "/api/tasks", "/api/checkpoints", "/api/task/<id>"],
    })


@app.get("/api/health")
def health():
    return jsonify({"ok": True, "db_exists": DB_PATH.exists(), "timestamp": iso(time.time())})


@app.get("/api/snapshot")
def api_snapshot():
    return jsonify(build_snapshot())


@app.get("/api/tasks")
def api_tasks():
    return jsonify(query_tasks())


@app.get("/api/checkpoints")
def api_checkpoints():
    return jsonify(query_checkpoints())


@app.get("/api/task/<path:task_id>")
def api_task_detail(task_id: str):
    tasks = query_tasks()
    for t in tasks:
        if t["id"] == task_id:
            t["details"] = extract_task_details(t)
            return jsonify(t)
    return jsonify({"error": "not found"}), 404


@app.get("/api/stream")
def api_stream():
    def generate():
        while True:
            payload = json.dumps(build_snapshot(), separators=(",", ":"))
            yield f"event: snapshot\ndata: {payload}\n\n"
            time.sleep(3)
    return Response(generate(), mimetype="text/event-stream")


# ---------------------------------------------------------------------------
# Agent process manager
# ---------------------------------------------------------------------------

class AgentProcessManager:
    """Manages a single subprocess running the agent choreography."""

    def __init__(self):
        self._proc: subprocess.Popen | None = None
        self._lock = threading.Lock()
        self._log_lines: list[dict] = []  # {ts, stream, text}
        self._max_lines = 5000
        self._subscribers: list[queue.Queue] = []

    @property
    def running(self) -> bool:
        with self._lock:
            return self._proc is not None and self._proc.poll() is None

    @property
    def status(self) -> dict:
        with self._lock:
            if self._proc is None:
                return {"state": "stopped", "pid": None, "exit_code": None}
            rc = self._proc.poll()
            if rc is None:
                return {"state": "running", "pid": self._proc.pid, "exit_code": None}
            return {"state": "exited", "pid": self._proc.pid, "exit_code": rc}

    def start(self, env_overrides: dict | None = None) -> dict:
        with self._lock:
            if self._proc is not None and self._proc.poll() is None:
                return {"error": "already running", "pid": self._proc.pid}

            # Find the venv python
            venv_python = ROOT / ".venv" / "bin" / "python"
            if not venv_python.exists():
                venv_python = Path(sys.executable)

            env = os.environ.copy()
            if env_overrides:
                env.update(env_overrides)

            self._log_lines.clear()
            self._proc = subprocess.Popen(
                [str(venv_python), "-u", "agents/verified_compiler_agents.py"],
                cwd=str(ROOT),
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                env=env,
                bufsize=1,
                text=True,
            )

            # Reader thread to capture output
            t = threading.Thread(target=self._read_output, daemon=True)
            t.start()

            return {"state": "started", "pid": self._proc.pid}

    def stop(self) -> dict:
        with self._lock:
            if self._proc is None or self._proc.poll() is not None:
                return {"state": "not_running"}
            pid = self._proc.pid
            self._proc.send_signal(signal.SIGINT)

        # Wait up to 5s for graceful shutdown, then kill
        try:
            self._proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            self._proc.kill()
            self._proc.wait(timeout=2)

        return {"state": "stopped", "pid": pid, "exit_code": self._proc.returncode}

    def get_log(self, after: int = 0) -> list[dict]:
        with self._lock:
            return self._log_lines[after:]

    def subscribe(self) -> queue.Queue:
        q: queue.Queue = queue.Queue(maxsize=200)
        with self._lock:
            self._subscribers.append(q)
        return q

    def unsubscribe(self, q: queue.Queue):
        with self._lock:
            try:
                self._subscribers.remove(q)
            except ValueError:
                pass

    def _read_output(self):
        proc = self._proc
        try:
            for raw_line in proc.stdout:
                line = raw_line.rstrip("\n")
                entry = {"ts": time.time(), "text": line}
                with self._lock:
                    self._log_lines.append(entry)
                    if len(self._log_lines) > self._max_lines:
                        self._log_lines = self._log_lines[-self._max_lines:]
                    dead = []
                    for q in self._subscribers:
                        try:
                            q.put_nowait(entry)
                        except queue.Full:
                            dead.append(q)
                    for q in dead:
                        try:
                            self._subscribers.remove(q)
                        except ValueError:
                            pass
        except Exception:
            pass
        finally:
            # Push an EOF sentinel
            eof = {"ts": time.time(), "text": None}
            with self._lock:
                for q in self._subscribers:
                    try:
                        q.put_nowait(eof)
                    except queue.Full:
                        pass


agent_proc = AgentProcessManager()


@app.post("/api/agents/start")
def api_agents_start():
    env = {}
    data = request.get_json(silent=True) or {}
    if data.get("model"):
        env["VERIFIEDJS_MODEL"] = data["model"]
    if data.get("max_cycles"):
        env["VERIFIEDJS_MAX_CYCLES"] = str(data["max_cycles"])
    result = agent_proc.start(env_overrides=env if env else None)
    return jsonify(result), 200 if "error" not in result else 409


@app.post("/api/agents/stop")
def api_agents_stop():
    return jsonify(agent_proc.stop())


@app.get("/api/agents/status")
def api_agents_status():
    return jsonify(agent_proc.status)


@app.get("/api/agents/log")
def api_agents_log():
    after = int(request.args.get("after", "0"))
    return jsonify(agent_proc.get_log(after=after))


@app.get("/api/agents/log/stream")
def api_agents_log_stream():
    """SSE stream of agent process stdout/stderr."""
    q = agent_proc.subscribe()

    def generate():
        try:
            while True:
                try:
                    entry = q.get(timeout=30)
                except queue.Empty:
                    yield ": keepalive\n\n"
                    continue
                if entry["text"] is None:
                    # Process exited
                    yield f"event: exit\ndata: {json.dumps(agent_proc.status)}\n\n"
                    break
                payload = json.dumps(entry, separators=(",", ":"))
                yield f"event: line\ndata: {payload}\n\n"
        finally:
            agent_proc.unsubscribe(q)

    return Response(generate(), mimetype="text/event-stream")


def build_frontend() -> bool:
    """Install npm deps and build the Svelte frontend."""
    if not FRONTEND_DIR.exists():
        print(f"[monitor] Frontend directory not found: {FRONTEND_DIR}")
        return False
    print("[monitor] Installing frontend dependencies...")
    r = subprocess.run(["npm", "install"], cwd=str(FRONTEND_DIR),
                       capture_output=True, text=True)
    if r.returncode != 0:
        print(f"[monitor] npm install failed:\n{r.stderr}")
        return False
    print("[monitor] Building frontend...")
    r = subprocess.run(["npx", "vite", "build"], cwd=str(FRONTEND_DIR),
                       capture_output=True, text=True)
    if r.returncode != 0:
        print(f"[monitor] vite build failed:\n{r.stderr}")
        return False
    print(f"[monitor] Frontend built -> {FRONTEND_DIST}")
    return True


def main():
    import argparse
    parser = argparse.ArgumentParser(description="VerifiedJS Agent Monitor")
    parser.add_argument("--host", default=os.environ.get("MONITOR_HOST", "127.0.0.1"))
    parser.add_argument("--port", type=int, default=int(os.environ.get("MONITOR_PORT", "5001")))
    parser.add_argument("--build", action="store_true", help="Build frontend before starting")
    parser.add_argument("--no-build", action="store_true", help="Skip frontend build check")
    args = parser.parse_args()

    # Auto-build if dist doesn't exist or --build flag
    if args.build or (not args.no_build and not (FRONTEND_DIST / "index.html").exists()):
        build_frontend()

    print(f"[monitor] Starting on http://{args.host}:{args.port}")
    print(f"[monitor] DB: {DB_PATH} (exists={DB_PATH.exists()})")
    app.run(host=args.host, port=args.port, debug=True, threaded=True)


if __name__ == "__main__":
    main()
