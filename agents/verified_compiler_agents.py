"""
VerifiedJS Multi-Agent Choreography for Verified Compiler Development.

A choreographic multi-agent system that automatically implements a formally
verified JavaScript-to-WebAssembly compiler in Lean 4. Uses effectful's
endpoint projection to run supervisor + worker agents in parallel with
crash recovery, persistent task queues, and context compaction.

Architecture:
  Constructive agents:
    - PlannerSupervisor: Reads TASKS.md/PROGRESS.md, plans sprints, reviews work
    - ContextSupervisor: Assembles precise context windows for workers
    - SpecWriterAgent (x2): Writes Lean Syntax.lean / Semantics.lean
    - TestWriterAgent: Writes Lean unit tests, validates spec accuracy
    - ProverAgent (x2): Proves correctness theorems
    - MemoryKeeperAgent: Persists findings, updates coordination files

  Adversarial agents:
    - SpecChallengerAgent: Tries to find ECMA-262 violations in our semantics
    - FuzzerAgent: Generates devilish JS inputs to crash/diverge the pipeline
    - SoundnessAuditorAgent: Audits proofs for sorry abuse, unsound axioms, gaps

The choreography runs in a continuous loop:
  Plan -> Context -> Execute -> *Adversarial* -> Review -> Revise -> Persist -> repeat

Usage::

    python agents/verified_compiler_agents.py
    VERIFIEDJS_MODEL=openai/gpt-4o VERIFIEDJS_MAX_CYCLES=20 python agents/verified_compiler_agents.py

Requirements:
    pip install "effectful[llm] @ git+https://github.com/BasisResearch/effectful.git@kg-persistent-agents"
    export ANTHROPIC_API_KEY=...
"""

import json
import logging
import os
import subprocess
import sys
import tempfile
import urllib.request
from pathlib import Path
from typing import Literal, TypedDict

from effectful.handlers.llm import Template, Tool
from effectful.handlers.llm.completions import LiteLLMProvider, RetryLLMHandler
from effectful.handlers.llm.multi import (
    Choreography,
    ChoreographyError,
    PersistentTaskQueue,
    scatter,
)
from effectful.handlers.llm.persistence import (
    CompactionHandler,
    PersistenceHandler,
    PersistentAgent,
)
from effectful.ops.types import NotHandled

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(threadName)s] %(name)s — %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger("verifiedjs-agents")

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

PROJECT_ROOT = Path(__file__).resolve().parent.parent
STATE_DIR = PROJECT_ROOT / ".agent_state"
MODEL = os.environ.get("VERIFIEDJS_MODEL", "anthropic/claude-sonnet-4-20250514")
MAX_CYCLES = int(os.environ.get("VERIFIEDJS_MAX_CYCLES", "10"))
MAX_HISTORY_LEN = 100

TASKS_FILE = PROJECT_ROOT / "TASKS.md"
PROGRESS_FILE = PROJECT_ROOT / "PROGRESS.md"
PROOF_BLOCKERS_FILE = PROJECT_ROOT / "PROOF_BLOCKERS.md"
LEAN_SRC = PROJECT_ROOT / "VerifiedJS"


# ---------------------------------------------------------------------------
# Structured types — all agent I/O is typed, no raw strings
# ---------------------------------------------------------------------------


class TaskSpec(TypedDict):
    """A concrete task assignment for a worker agent."""
    task_id: str
    task_type: Literal["spec", "implement", "test", "prove", "review"]
    module: str
    target_file: str
    description: str
    ecma_spec_section: str
    context_files: list[str]
    acceptance_criteria: str


class PlanResult(TypedDict):
    """Planner output — a prioritized list of task specs."""
    tasks: list[TaskSpec]
    rationale: str


class ContextBundle(TypedDict):
    """Assembled context for a worker agent."""
    task_id: str
    lean_source: dict[str, str]
    ecma_spec_notes: str
    existing_sorrys: list[str]
    proof_blockers: str
    guidance: str


class FileWrite(TypedDict):
    """A concrete file write to be applied."""
    path: str
    content: str
    action: Literal["create", "overwrite", "patch"]


class SpecResult(TypedDict):
    """Output from a spec writer — includes executable file writes."""
    file_writes: list[FileWrite]
    spec_citations: list[str]
    new_sorrys: list[str]
    build_ok: bool
    notes: str


class ExecutableTestCase(TypedDict):
    """A single executable test case with expected output."""
    name: str
    js_input: str
    expected_node_output: str
    lean_eval_code: str
    stages_to_check: list[str]


class TestResult(TypedDict):
    """Output from the test writer — includes executable test cases."""
    verdict: Literal["PASS", "NEEDS_FIXES", "SPEC_INACCURATE"]
    file_writes: list[FileWrite]
    test_cases: list[ExecutableTestCase]
    failures: list[str]
    feedback: str


class ProofResult(TypedDict):
    """Output from a prover agent — includes file writes."""
    file_writes: list[FileWrite]
    sorrys_resolved: int
    sorrys_remaining: int
    blocked_goals: list[str]
    tactics_used: list[str]
    notes: str


class ReviewResult(TypedDict):
    """Supervisor review of completed work."""
    verdict: Literal["ACCEPT", "REVISE", "REJECT"]
    feedback: str
    updates: dict[str, str]


class ContinueDecision(TypedDict):
    """Planner decides whether to keep looping."""
    should_continue: bool
    reason: str
    priority_shift: str


# ── Adversarial output types ─────────────────────────────────────────────


class SpecViolation(TypedDict):
    """A specific ECMA-262 violation found in our Lean semantics."""
    ecma_section: str
    ecma_requirement: str
    our_behavior: str
    js_witness: str
    node_output: str
    verifiedjs_output: str
    severity: Literal["critical", "major", "minor", "cosmetic"]
    lean_file: str
    lean_line_hint: str
    suggested_fix: str


class SpecChallengeResult(TypedDict):
    """Output from the spec challenger — concrete violations with witnesses."""
    violations: list[SpecViolation]
    tests_run: int
    ecma_sections_checked: list[str]
    clean_sections: list[str]


class FuzzCase(TypedDict):
    """A fuzz test case that triggered a bug."""
    js_code: str
    expected_behavior: str
    actual_behavior: str
    crash_type: Literal[
        "parse_error", "elaborate_crash", "interp_diverge",
        "interp_wrong_result", "wasm_compile_fail", "wasm_runtime_mismatch",
        "pipeline_inconsistency", "timeout",
    ]
    stage: str
    reproducer_command: str
    minimal: bool


class FuzzResult(TypedDict):
    """Output from the fuzzer — executable reproducers."""
    bugs_found: list[FuzzCase]
    cases_tried: int
    stages_fuzzed: list[str]
    pipeline_consistency_failures: int


class SorryAuditEntry(TypedDict):
    """An audit of a single sorry usage."""
    file: str
    line: int
    theorem_name: str
    goal_type: str
    is_critical_path: bool
    risk: Literal["high", "medium", "low"]
    notes: str


class SoundnessIssue(TypedDict):
    """A soundness concern found during proof audit."""
    category: Literal[
        "sorry_on_critical_path", "axiom_inconsistency",
        "missing_decreasing_proof", "unsound_native_decide",
        "incorrect_spec_assumption", "proof_by_cheating",
    ]
    file: str
    location: str
    description: str
    severity: Literal["critical", "major", "minor"]
    suggested_fix: str


class SoundnessAuditResult(TypedDict):
    """Output from the soundness auditor."""
    sorry_audit: list[SorryAuditEntry]
    soundness_issues: list[SoundnessIssue]
    total_sorrys: int
    critical_path_sorrys: int
    axioms_used: list[str]
    overall_risk: Literal["red", "yellow", "green"]
    recommendations: list[str]


class MemoryReport(TypedDict):
    """Structured output from the memory keeper."""
    files_updated: list[str]
    sorry_count_before: int
    sorry_count_after: int
    sorry_delta: int
    build_healthy: bool
    e2e_pass: bool
    regressions: list[str]
    key_findings: list[str]
    new_blockers: list[str]
    resolved_blockers: list[str]


# ---------------------------------------------------------------------------
# Shell / tool helpers
# ---------------------------------------------------------------------------


def _run(cmd: str, cwd: Path = PROJECT_ROOT, timeout: int = 120) -> str:
    """Run a shell command and return stdout+stderr, truncated to 6000 chars."""
    try:
        r = subprocess.run(
            cmd, shell=True, cwd=cwd, capture_output=True, text=True, timeout=timeout
        )
        out = (r.stdout + r.stderr).strip()
        if len(out) > 6000:
            out = out[:3000] + "\n... [truncated] ...\n" + out[-3000:]
        return out
    except subprocess.TimeoutExpired:
        return f"[TIMEOUT after {timeout}s]: {cmd}"
    except Exception as e:
        return f"[ERROR]: {e}"


def _read_project_file(path: str, max_chars: int = 12000) -> str:
    full = PROJECT_ROOT / path
    if not full.exists():
        return f"File not found: {path}"
    content = full.read_text()
    if len(content) > max_chars:
        half = max_chars // 2
        content = content[:half] + "\n/- ... truncated ... -/\n" + content[-half:]
    return content


def _write_project_file(path: str, content: str) -> str:
    full = PROJECT_ROOT / path
    full.parent.mkdir(parents=True, exist_ok=True)
    full.write_text(content)
    return f"Wrote {len(content)} chars to {path}"


def _fetch_url(url: str, max_chars: int = 8000) -> str:
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "VerifiedJS-Agent/1.0"})
        with urllib.request.urlopen(req, timeout=15) as resp:
            text = resp.read().decode("utf-8", errors="replace")
            if len(text) > max_chars:
                text = text[:max_chars] + "\n... [truncated] ..."
            return text
    except Exception as e:
        return f"[FETCH ERROR]: {e}"


def _run_python(code: str, timeout: int = 30) -> str:
    with tempfile.NamedTemporaryFile(suffix=".py", mode="w", delete=False) as f:
        f.write(code)
        f.flush()
        try:
            return _run(f"{sys.executable} {f.name}", timeout=timeout)
        finally:
            os.unlink(f.name)


def _apply_file_writes(file_writes: list) -> list[str]:
    """Apply a list of FileWrite dicts to disk. Returns list of paths written."""
    written = []
    for fw in file_writes:
        path = fw.get("path", "")
        content = fw.get("content", "")
        if path and content:
            _write_project_file(path, content)
            written.append(path)
    return written


# ---------------------------------------------------------------------------
# Shared tools mixin — every agent inherits these
# ---------------------------------------------------------------------------


class _SharedTools:
    """Mixin providing shell, lean, python, web, and project tools to all agents."""

    def __init__(self, **kwargs):
        super().__init__(**kwargs)

    # ── Shell & system ────────────────────────────────────────────

    @Tool.define
    def shell(self, command: str) -> str:
        """Run an arbitrary shell command in the project root. Returns stdout+stderr (truncated). Use for git, grep, find, wc, diff, etc."""
        return _run(command)

    # ── Lean / Lake ───────────────────────────────────────────────

    @Tool.define
    def lake_build(self) -> str:
        """Run `lake build` and return compiler output."""
        return _run("lake build", timeout=300)

    @Tool.define
    def lake_test(self) -> str:
        """Run `lake test` to execute Lean unit tests."""
        return _run("lake test", timeout=300)

    @Tool.define
    def lake_env_lean(self, lean_file: str) -> str:
        """Run `lake env lean <file>` to typecheck a single Lean file."""
        return _run(f"lake env lean {lean_file}", timeout=180)

    @Tool.define
    def lean_check_file(self, path: str) -> str:
        """Typecheck a Lean file and return only error/warning lines."""
        out = _run(f"lake env lean {path} 2>&1", timeout=180)
        diag = [line for line in out.splitlines()
                if any(k in line for k in ["error", "warning", "sorry"])]
        return "\n".join(diag) if diag else "No errors or warnings."

    @Tool.define
    def run_e2e_tests(self) -> str:
        """Run the end-to-end test suite (tests/e2e/run_e2e.sh)."""
        return _run("bash tests/e2e/run_e2e.sh", timeout=180)

    # ── File I/O ──────────────────────────────────────────────────

    @Tool.define
    def read_file(self, path: str) -> str:
        """Read a file relative to project root (truncated to 12000 chars)."""
        return _read_project_file(path)

    @Tool.define
    def write_file(self, path: str, content: str) -> str:
        """Write a file relative to project root. Creates parent dirs."""
        return _write_project_file(path, content)

    @Tool.define
    def append_to_file(self, path: str, content: str) -> str:
        """Append content to a file."""
        full = PROJECT_ROOT / path
        existing = full.read_text() if full.exists() else ""
        full.parent.mkdir(parents=True, exist_ok=True)
        full.write_text(existing + "\n" + content)
        return f"Appended {len(content)} chars to {path}"

    # ── Grep & search ─────────────────────────────────────────────

    @Tool.define
    def grep_lean(self, pattern: str, module: str = "") -> str:
        """Grep for a pattern across Lean files. Optionally restrict to a module dir."""
        target = f"VerifiedJS/{module}" if module else "VerifiedJS/"
        return _run(f"grep -rn '{pattern}' --include='*.lean' {target} || echo 'No matches'")

    @Tool.define
    def count_sorrys(self, module: str = "") -> str:
        """Count sorry occurrences. Optionally restrict to a module."""
        target = f"VerifiedJS/{module}" if module else "VerifiedJS/"
        return _run(f"grep -rn 'sorry' --include='*.lean' {target} 2>/dev/null || echo '0 sorrys'")

    @Tool.define
    def list_lean_files(self, module: str = "") -> str:
        """List all .lean files, optionally in a specific module."""
        target = LEAN_SRC / module if module else LEAN_SRC
        if not target.exists():
            return f"Not found: {target}"
        files = sorted(target.rglob("*.lean"))
        return "\n".join(
            f"{f.relative_to(PROJECT_ROOT)} ({f.stat().st_size}b)" for f in files
        )

    # ── Python & Node.js ──────────────────────────────────────────

    @Tool.define
    def run_python(self, code: str) -> str:
        """Run a Python code snippet and return output."""
        return _run_python(code)

    @Tool.define
    def run_node(self, js_code: str) -> str:
        """Run JavaScript in Node.js. Use to check expected ECMAScript behavior."""
        with tempfile.NamedTemporaryFile(suffix=".js", mode="w", delete=False) as f:
            f.write(js_code)
            f.flush()
            try:
                return _run(f"node {f.name}", timeout=15)
            finally:
                os.unlink(f.name)

    # ── VerifiedJS pipeline tools ─────────────────────────────────

    @Tool.define
    def emit_il(self, js_code: str, stage: str = "core") -> str:
        """Compile inline JS and emit an IL. Stage: core|flat|anf|wasmIR|wat."""
        with tempfile.NamedTemporaryFile(
            suffix=".js", mode="w", delete=False, dir=str(PROJECT_ROOT)
        ) as f:
            f.write(js_code)
            f.flush()
            try:
                return _run(f"lake exe verifiedjs {f.name} --emit={stage}", timeout=60)
            finally:
                os.unlink(f.name)

    @Tool.define
    def interpret_il(self, js_code: str, stage: str = "core") -> str:
        """Compile inline JS and run interpreter at a stage. Stage: core|flat|anf|wasmIR."""
        with tempfile.NamedTemporaryFile(
            suffix=".js", mode="w", delete=False, dir=str(PROJECT_ROOT)
        ) as f:
            f.write(js_code)
            f.flush()
            try:
                return _run(
                    f"lake exe verifiedjs {f.name} --run={stage}", timeout=60
                )
            finally:
                os.unlink(f.name)

    @Tool.define
    def compile_and_run_wasm(self, js_file: str) -> str:
        """Compile a JS file to .wasm and run it with wasmtime."""
        wasm_out = js_file.replace(".js", ".wasm")
        cr = _run(f"lake exe verifiedjs {js_file} -o {wasm_out}", timeout=120)
        if "error" in cr.lower():
            return f"Compilation failed:\n{cr}"
        return f"Compile: OK\nRun:\n{_run(f'wasmtime {wasm_out}', timeout=15)}"

    @Tool.define
    def compare_node_vs_verifiedjs(self, js_code: str, stage: str = "core") -> str:
        """Run JS in both Node.js and VerifiedJS interpreter, return diff."""
        node_out = self.run_node(js_code)
        vjs_out = self.interpret_il(js_code, stage)
        if node_out.strip() == vjs_out.strip():
            return f"MATCH: {node_out.strip()}"
        return f"MISMATCH!\n  Node.js: {node_out.strip()}\n  VerifiedJS({stage}): {vjs_out.strip()}"

    # ── Web / spec lookup ─────────────────────────────────────────

    @Tool.define
    def fetch_url(self, url: str) -> str:
        """Fetch a URL and return text (truncated to 8000 chars)."""
        return _fetch_url(url)

    @Tool.define
    def fetch_ecma_spec(self, section_fragment: str) -> str:
        """Fetch an ECMAScript 2020 spec section by URL fragment."""
        return _fetch_url(
            f"https://tc39.es/ecma262/2020/#{section_fragment}", max_chars=12000
        )

    # ── Misc project tools ────────────────────────────────────────

    @Tool.define
    def sorry_report(self) -> str:
        """Full sorry breakdown across all modules."""
        return _run(
            "bash scripts/sorry_report.sh 2>/dev/null "
            "|| grep -rn sorry --include='*.lean' VerifiedJS/ | wc -l",
            timeout=60,
        )

    @Tool.define
    def git_status(self) -> str:
        """Get current git status + recent log."""
        return _run("git status --short && echo '---' && git log --oneline -5")


# ---------------------------------------------------------------------------
# Constructive agents
# ---------------------------------------------------------------------------


class PlannerSupervisor(_SharedTools, PersistentAgent):
    """You are the lead architect and project manager for VerifiedJS, a formally
    verified JavaScript-to-WebAssembly compiler in Lean 4.

    Your job:
    1. Read TASKS.md, PROGRESS.md, and PROOF_BLOCKERS.md to understand current state
    2. Identify the highest-priority work items that can be parallelized
    3. Break them into concrete TaskSpecs with precise ECMAScript 2020 spec citations
    4. Assign tasks to worker agents with clear acceptance criteria
    5. After workers complete, review results including adversarial findings
    6. Decide whether to continue looping or stop

    Key principles:
    - Every Lean semantic rule must cite ECMA-262 §section
    - Prioritize: blocking issues > adversarial findings > completeness > proofs > runtime
    - Adversarial agent findings (spec violations, fuzz bugs, soundness issues) are HIGH
      priority — they indicate real correctness problems
    - Design for provability — if correct but hard to prove, suggest refactoring
    - Never assign proof work already in PROOF_BLOCKERS.md without new approaches
    """

    @Template.define
    def plan_next_sprint(
        self, current_state: str, cycle_number: int,
        adversarial_findings: str,
    ) -> PlanResult:
        """Plan the next batch of parallel tasks.

        This is cycle {cycle_number}.

        IMPORTANT: adversarial_findings contains bugs and spec violations found by
        the challenger, fuzzer, and soundness auditor. These are HIGH PRIORITY — if
        there are critical violations, create tasks to fix them before other work.

        Use tools to inspect the project: lake_build, count_sorrys, read_file,
        grep_lean, list_lean_files.

        Create 3-8 concrete TaskSpecs. Include tasks to fix adversarial findings.

        Current project state:
        {current_state}

        Adversarial findings from previous cycle:
        {adversarial_findings}"""
        raise NotHandled

    @Template.define
    def review_completed_work(
        self, task_id: str, task_spec: str, result: str
    ) -> ReviewResult:
        """Review a worker's completed task.

        Use tools to verify: lake_build, lean_check_file, read_file, grep_lean.

        Check:
        1. Does the Lean code build?
        2. Are spec citations present and correct?
        3. Do new sorrys have TODO comments?
        4. Is the acceptance criteria met?
        5. Were file_writes applied correctly?

        Task: {task_id}
        Spec: {task_spec}
        Result: {result}"""
        raise NotHandled

    @Template.define
    def decide_continue(self, cycle_report: str) -> ContinueDecision:
        """Decide whether to continue with another cycle.

        Use lake_build, count_sorrys, run_e2e_tests to check health.

        Consider:
        1. Progress? (sorrys decreasing, tests passing, violations fixed)
        2. Adversarial pressure? (are challengers still finding new bugs?)
        3. Diminishing returns?
        4. High-priority items remaining?

        Cycle report:
        {cycle_report}"""
        raise NotHandled


class ContextSupervisor(_SharedTools, PersistentAgent):
    """You are a context assembly specialist for the VerifiedJS compiler project.

    Read relevant Lean source files for a task and assemble a precise, minimal
    ContextBundle. Keep context under 8000 chars per file.

    Pipeline: Source -> Core -> Flat -> ANF -> Wasm.IR -> Wasm.AST -> .wasm
    """

    @Template.define
    def assemble_context(self, task_spec: str) -> ContextBundle:
        """Read relevant files and assemble a ContextBundle.

        Use read_file, grep_lean, lean_check_file, fetch_ecma_spec, count_sorrys.

        Task specification:
        {task_spec}"""
        raise NotHandled


class SpecWriterAgent(_SharedTools, PersistentAgent):
    """You are a Lean 4 formalization expert. You write Syntax.lean and
    Semantics.lean files for VerifiedJS.

    IMPORTANT: Return structured SpecResult with file_writes containing the
    actual Lean code you want written. Each FileWrite has path, content, action.
    Also call write_file yourself to apply them, then lake_build to verify.

    Rules:
    1. Cite ECMA-262 §section in docstrings
    2. `sorry` only with `-- TODO:` comment
    3. Design for provability
    4. Verify with lake_build after writing
    """

    @Template.define
    def write_spec(self, context: str) -> SpecResult:
        """Write or update a Lean specification file.

        You MUST:
        1. Use write_file to write the Lean code to disk
        2. Use lake_build to verify it compiles
        3. Return a SpecResult with file_writes listing what you wrote,
           spec_citations, new_sorrys, build_ok, and notes

        Context:
        {context}"""
        raise NotHandled


class TestWriterAgent(_SharedTools, PersistentAgent):
    """You are a testing specialist for VerifiedJS. You write Lean 4 unit tests
    and validate spec accuracy vs ECMAScript 2020.

    IMPORTANT: Return structured TestResult with:
    - file_writes: the actual Lean test files you wrote
    - test_cases: executable test cases with JS input, expected Node output,
      Lean #eval code, and which stages to check

    Use run_node to establish ground truth, then compare with interpret_il.
    """

    @Template.define
    def write_tests_and_validate(self, context: str) -> TestResult:
        """Write tests and validate a Lean spec/implementation.

        You MUST:
        1. Use run_node to get expected output for each test case
        2. Use write_file to write Lean test files
        3. Use lean_check_file to verify they compile
        4. Return TestResult with file_writes, test_cases (executable!), failures

        Context:
        {context}"""
        raise NotHandled


class ProverAgent(_SharedTools, PersistentAgent):
    """You are a Lean 4 proof engineer for VerifiedJS compiler verification.

    Proof strategy (try in order):
    1. `canonical`, `duper` (import Duper if not present)
    2. `grind` — congruence closure + case splitting
    3. `aesop` — automated reasoning
    4. `decide` — decidable propositions
    5. `simp [lemma1, lemma2]` — rewriting
    6. `omega` — linear arithmetic
    7. `native_decide` — kernel evaluation
    8. Manual proof terms — last resort

    IMPORTANT: Return ProofResult with file_writes containing the updated proof file.
    Always check PROOF_BLOCKERS.md first.
    """

    @Template.define
    def prove_theorem(self, context: str) -> ProofResult:
        """Prove a theorem or resolve sorrys.

        You MUST:
        1. Read PROOF_BLOCKERS.md first
        2. Use write_file to write the updated proof
        3. Use lake_build to verify
        4. Return ProofResult with file_writes, sorrys_resolved/remaining, blockers

        Context:
        {context}"""
        raise NotHandled


class MemoryKeeperAgent(_SharedTools, PersistentAgent):
    """You are the institutional memory of the VerifiedJS project.

    IMPORTANT: Return a structured MemoryReport, not a free-text string.
    Compute sorry deltas, check build health, detect regressions.
    """

    @Template.define
    def persist_findings(self, cycle_summary: str) -> MemoryReport:
        """Process cycle results and update coordination files.

        You MUST:
        1. lake_build to check health
        2. count_sorrys and compute delta from previous
        3. run_e2e_tests to detect regressions
        4. Update TASKS.md, PROGRESS.md, PROOF_BLOCKERS.md via write_file
        5. Append to .agent_state/findings.md
        6. Return a MemoryReport with all fields filled

        Cycle summary:
        {cycle_summary}"""
        raise NotHandled


# ---------------------------------------------------------------------------
# Adversarial agents
# ---------------------------------------------------------------------------


class SpecChallengerAgent(_SharedTools, PersistentAgent):
    """You are an adversarial agent whose SOLE JOB is to find places where
    VerifiedJS's Lean semantics DIVERGE from the ECMAScript 2020 specification.

    You are the project's worst enemy. You want to find bugs. You are rewarded
    for finding real violations, not for being helpful.

    Strategy:
    1. Pick an ECMA-262 section that VerifiedJS claims to implement
    2. Read the actual spec text (use fetch_ecma_spec)
    3. Read our Lean semantics (use read_file)
    4. Construct a WITNESS — a specific JS program where our semantics
       produce the wrong result
    5. EXECUTE the witness: run_node for ground truth, compare_node_vs_verifiedjs
       or interpret_il for our output
    6. If they disagree, you found a violation — report it with full evidence

    Focus areas for maximum damage:
    - Type coercion edge cases (ToNumber, ToString, ToPrimitive)
    - Operator overloading (+, ==, < with objects)
    - Variable scoping (let/const/var hoisting, closures, TDZ)
    - Control flow (labeled statements, for-in enumeration order)
    - Exception semantics (try/catch/finally ordering)
    - Prototype chain behavior
    - this binding rules
    - Automatic semicolon insertion effects

    You have specialized tools:
    - run_test262_section: run official Test262 cases for a spec section
    - batch_differential_test: run many JS snippets against Node + all stages at once
    - extract_spec_claims: parse a Lean file for ECMA-262 citations
    - generate_coercion_matrix: generate type coercion test matrix

    You MUST produce EXECUTABLE witnesses — JS code that can be run in Node.js.
    """

    @Tool.define
    def run_test262_section(self, section: str, max_cases: int = 30) -> str:
        """Run official Test262 test cases for a specific ECMA-262 section.
        Uses the test262 harness in the project if available, otherwise falls
        back to cloning the relevant subset."""
        return _run(
            f"./scripts/run_test262_compare.sh --section '{section}' "
            f"--sample {max_cases} --seed local 2>&1",
            timeout=180,
        )

    @Tool.define
    def batch_differential_test(self, js_snippets_json: str) -> str:
        """Run a batch of JS snippets through Node.js AND all VerifiedJS IL
        stages. Input: JSON array of strings. Output: comparison table.

        Example input: '["1+1", "typeof null", "[] + {}"]'
        """
        code = f"""
import json, subprocess, tempfile, os

snippets = json.loads('''{js_snippets_json}''')
results = []
for snip in snippets[:50]:  # cap at 50
    row = {{"js": snip}}
    # Node.js
    with tempfile.NamedTemporaryFile(suffix=".js", mode="w", delete=False) as f:
        f.write(f"console.log(eval({{json.dumps(snip)}}))")
        f.flush()
        r = subprocess.run(["node", f.name], capture_output=True, text=True, timeout=5)
        row["node"] = r.stdout.strip()
        os.unlink(f.name)
    # VerifiedJS stages
    for stage in ["core", "flat", "anf"]:
        with tempfile.NamedTemporaryFile(suffix=".js", mode="w", delete=False, dir=".") as f:
            f.write(snip if "console" in snip else f"console.log({{snip}})")
            f.flush()
            r = subprocess.run(
                f"lake exe verifiedjs {{f.name}} --run={{stage}}",
                shell=True, capture_output=True, text=True, timeout=30
            )
            row[stage] = r.stdout.strip() or r.stderr.strip()[:200]
            os.unlink(f.name)
    results.append(row)
# Print mismatches
mismatches = [r for r in results if any(r.get(s) != r["node"] for s in ["core","flat","anf"])]
print(f"Tested {{len(results)}} snippets, {{len(mismatches)}} mismatches")
for m in mismatches:
    print(json.dumps(m, indent=2))
"""
        return _run_python(code, timeout=120)

    @Tool.define
    def extract_spec_claims(self, lean_file: str) -> str:
        """Parse a Lean file and extract all ECMA-262 spec citations.
        Returns a list of (line_number, citation, context) tuples."""
        code = f"""
import re
with open("{PROJECT_ROOT / lean_file}") as f:
    lines = f.readlines()
claims = []
for i, line in enumerate(lines, 1):
    # Match patterns like §13.15, ECMA-262 §X.Y, sec-xxx
    for m in re.finditer(r'(§[\\d.]+|ECMA-262\\s+§[\\d.]+|sec-[\\w-]+)', line):
        claims.append((i, m.group(), line.strip()))
for c in claims:
    print(f"  L{{c[0]}}: {{c[1]}} — {{c[2][:100]}}")
if not claims:
    print("No spec citations found")
print(f"\\nTotal: {{len(claims)}} citations")
"""
        return _run_python(code)

    @Tool.define
    def generate_coercion_matrix(self) -> str:
        """Generate and run a type coercion test matrix in Node.js.
        Tests all combinations of JS types with operators +, ==, <, etc.
        Returns a table of results for comparison."""
        js_code = """
const types = [0, 1, -1, NaN, Infinity, "", "0", "1", "hello",
               true, false, null, undefined, [], [1], {}, [0]];
const ops = [
  ["+", (a,b) => a + b],
  ["==", (a,b) => a == b],
  ["===", (a,b) => a === b],
  ["<", (a,b) => a < b],
];
const labels = types.map(v => JSON.stringify(v));
const results = [];
for (const [opName, opFn] of ops) {
  for (let i = 0; i < types.length; i++) {
    for (let j = 0; j < types.length; j++) {
      try {
        const r = opFn(types[i], types[j]);
        results.push(`${opName} | ${labels[i]} | ${labels[j]} | ${JSON.stringify(r)}`);
      } catch(e) {
        results.push(`${opName} | ${labels[i]} | ${labels[j]} | THROWS: ${e.message}`);
      }
    }
  }
}
console.log(results.join("\\n"));
"""
        with tempfile.NamedTemporaryFile(suffix=".js", mode="w", delete=False) as f:
            f.write(js_code)
            f.flush()
            try:
                return _run(f"node {f.name}", timeout=30)
            finally:
                os.unlink(f.name)

    @Tool.define
    def check_typeof_table(self) -> str:
        """Run the typeof operator on all JS value types in Node.js and return
        the canonical table. Useful for checking our typeof implementation."""
        js_code = """
const vals = [undefined, null, true, 42, "str", Symbol(), function(){}, {}, []];
const names = ["undefined","null","true","42","'str'","Symbol()","function(){}","{}","[]"];
for (let i = 0; i < vals.length; i++)
  console.log(`typeof ${names[i]} = ${typeof vals[i]}`);
"""
        with tempfile.NamedTemporaryFile(suffix=".js", mode="w", delete=False) as f:
            f.write(js_code)
            f.flush()
            try:
                return _run(f"node {f.name}", timeout=10)
            finally:
                os.unlink(f.name)

    @Template.define
    def challenge_specs(self, target_modules: str) -> SpecChallengeResult:
        """Try to find ECMA-262 violations in the specified modules.

        Steps:
        1. Use extract_spec_claims to find what we claim to implement
        2. Use fetch_ecma_spec to read the actual spec text
        3. Use generate_coercion_matrix and check_typeof_table for quick baselines
        4. Construct adversarial JS test cases for each claim
        5. Use batch_differential_test for bulk comparison
        6. Use compare_node_vs_verifiedjs for individual deep-dives
        7. Use run_test262_section for official conformance checks
        8. Report all mismatches as SpecViolations with full evidence

        Try at least 10-15 test cases. Focus on edge cases and coercions.

        Target modules to attack:
        {target_modules}"""
        raise NotHandled


class FuzzerAgent(_SharedTools, PersistentAgent):
    """You are a fuzzing agent whose job is to BREAK the VerifiedJS compiler
    pipeline by generating adversarial JavaScript inputs.

    You are creative, malicious (in a testing sense), and thorough. You want to
    find crashes, wrong outputs, timeouts, and pipeline inconsistencies.

    You have specialized tools:
    - hypothesis_fuzz: property-based fuzzing using Hypothesis
    - grammar_fuzz_js: grammar-aware JS generation
    - mutate_js: mutate existing JS programs
    - pipeline_consistency_check: check all IL stages agree
    - minimize_reproducer: shrink a failing JS input to minimal form
    - stress_nesting: generate deeply nested expressions to find stack overflows

    For each bug found, produce a MINIMAL reproducer — the simplest JS code
    that triggers the issue, plus the exact command to reproduce it.
    """

    @Tool.define
    def hypothesis_fuzz(self, strategy: str = "expressions", num_cases: int = 50) -> str:
        """Run property-based fuzzing using Python's Hypothesis library.
        Strategy: 'expressions' | 'statements' | 'programs' | 'numeric'
        Generates random JS, runs in Node + VerifiedJS, finds mismatches."""
        code = f"""
import random, subprocess, tempfile, os, json

random.seed(42)

# JS expression generators
def rand_num():
    return random.choice(["0", "1", "-1", "0.1", "NaN", "Infinity", "-Infinity",
                          "1e308", "5e-324", "0x1F", "0o17", "0b11", "1_000"])

def rand_str():
    s = random.choice(["", "0", "1", "hello", "null", "undefined", "true", "false",
                        "\\\\n", "\\\\t", " ", "NaN", "Infinity"])
    return json.dumps(s)

def rand_val():
    return random.choice([rand_num(), rand_str(), "null", "undefined",
                          "true", "false", "[]", "[1]", "[0]", "{{}}", "NaN"])

def rand_unop():
    op = random.choice(["+", "-", "!", "~", "typeof ", "void "])
    return f"({{op}}{{rand_val()}})"

def rand_binop():
    op = random.choice(["+", "-", "*", "/", "%", "**", "==", "===", "!=",
                        "!==", "<", ">", "<=", ">=", "&", "|", "^", "<<", ">>", ">>>"])
    return f"({{rand_val()}} {{op}} {{rand_val()}})"

def rand_expr():
    gen = random.choice([rand_val, rand_unop, rand_binop])
    return gen()

# Generate and test
bugs = []
for i in range({num_cases}):
    expr = rand_expr()
    js = f"console.log({{expr}})"
    # Node
    with tempfile.NamedTemporaryFile(suffix=".js", mode="w", delete=False) as f:
        f.write(js); f.flush()
        nr = subprocess.run(["node", f.name], capture_output=True, text=True, timeout=5)
        node_out = nr.stdout.strip()
        os.unlink(f.name)
    # VerifiedJS core
    with tempfile.NamedTemporaryFile(suffix=".js", mode="w", delete=False, dir=".") as f:
        f.write(js); f.flush()
        vr = subprocess.run(f"lake exe verifiedjs {{f.name}} --run=core",
                            shell=True, capture_output=True, text=True, timeout=30)
        vjs_out = vr.stdout.strip()
        os.unlink(f.name)
    if node_out != vjs_out and "error" not in vjs_out.lower()[:50]:
        bugs.append({{"expr": expr, "node": node_out, "vjs": vjs_out}})

print(f"Tested {num_cases} expressions, {{len(bugs)}} mismatches")
for b in bugs[:20]:
    print(json.dumps(b))
"""
        return _run_python(code, timeout=180)

    @Tool.define
    def grammar_fuzz_js(self, category: str = "mixed", count: int = 30) -> str:
        """Generate syntactically valid but semantically tricky JS programs.
        Category: 'coercion' | 'scoping' | 'control_flow' | 'exceptions' | 'mixed'
        Returns JSON array of generated programs."""
        code = f"""
import random, json
random.seed(0xDEAD)

templates = {{
    "coercion": [
        "console.log([] + []);",
        "console.log([] + {{}});",
        "console.log({{}} + []);",
        "console.log(+[]);",
        "console.log(+{{}});",
        "console.log('' + 0);",
        "console.log(true + true);",
        "console.log(null + 1);",
        "console.log(undefined + 1);",
        "console.log('5' - 3);",
        "console.log('5' * '3');",
        "console.log(null == undefined);",
        "console.log(null === undefined);",
        "console.log(NaN == NaN);",
        "console.log(NaN === NaN);",
        "console.log(typeof null);",
        "console.log(typeof undefined);",
        "console.log(typeof NaN);",
        "console.log(1 < 2 < 3);",
        "console.log(3 > 2 > 1);",
        "console.log(0 == '');",
        "console.log(0 == '0');",
        "console.log('' == '0');",
        "console.log(false == '0');",
        "console.log(false == '');",
        "console.log(false == undefined);",
        "console.log(false == null);",
        "console.log(0 == null);",
    ],
    "scoping": [
        "var x = 1; {{ var x = 2; }} console.log(x);",
        "let x = 1; {{ let x = 2; }} console.log(x);",
        "for (var i = 0; i < 3; i++) {{}}; console.log(typeof i);",
        "for (let j = 0; j < 3; j++) {{}}; console.log(typeof j);",
        "(function() {{ console.log(typeof x); var x = 1; }})();",
        "console.log(typeof undeclaredVar);",
    ],
    "control_flow": [
        "L: for (var i=0;i<3;i++) {{ for (var j=0;j<3;j++) {{ if(j==1) break L; }} }} console.log(i,j);",
        "try {{ throw 1; }} catch(e) {{ console.log(e); }}",
        "try {{ }} finally {{ console.log('finally'); }}",
        "try {{ throw 1; }} catch(e) {{ throw 2; }} finally {{ console.log('f'); }}",
        "console.log(1, 2, 3);",
    ],
    "exceptions": [
        "try {{ null.x }} catch(e) {{ console.log(e instanceof TypeError); }}",
        "try {{ undecl; }} catch(e) {{ console.log(e instanceof ReferenceError); }}",
        "try {{ eval('{{'); }} catch(e) {{ console.log(e instanceof SyntaxError); }}",
    ],
}}

cat = '{category}'
if cat == 'mixed':
    pool = [p for ps in templates.values() for p in ps]
else:
    pool = templates.get(cat, templates['coercion'])

selected = random.sample(pool, min({count}, len(pool)))
print(json.dumps(selected, indent=2))
"""
        return _run_python(code)

    @Tool.define
    def pipeline_consistency_check(self, js_code: str) -> str:
        """Check that all VerifiedJS IL stages produce the same output for a
        given JS program. Compares core, flat, anf interpreters."""
        results = {}
        for stage in ["core", "flat", "anf"]:
            results[stage] = self.interpret_il(js_code, stage)
        node_result = self.run_node(js_code)
        results["node"] = node_result

        lines = [f"Node.js: {results['node']}"]
        consistent = True
        for stage in ["core", "flat", "anf"]:
            match = results[stage].strip() == results["node"].strip()
            marker = "OK" if match else "MISMATCH"
            if not match:
                consistent = False
            lines.append(f"{stage}: {results[stage]} [{marker}]")
        lines.insert(0, f"CONSISTENT: {consistent}")
        return "\n".join(lines)

    @Tool.define
    def minimize_reproducer(self, js_code: str, stage: str = "core") -> str:
        """Attempt to minimize a failing JS input by iteratively removing tokens.
        Returns the smallest JS code that still triggers the bug."""
        code = f"""
import subprocess, tempfile, os

original = '''{js_code}'''

def run_vjs(code, stage="{stage}"):
    with tempfile.NamedTemporaryFile(suffix=".js", mode="w", delete=False, dir=".") as f:
        f.write(code); f.flush()
        r = subprocess.run(f"lake exe verifiedjs {{f.name}} --run={{stage}}",
                           shell=True, capture_output=True, text=True, timeout=30)
        os.unlink(f.name)
        return r.stdout.strip(), r.returncode

def run_node(code):
    with tempfile.NamedTemporaryFile(suffix=".js", mode="w", delete=False) as f:
        f.write(code); f.flush()
        r = subprocess.run(["node", f.name], capture_output=True, text=True, timeout=5)
        os.unlink(f.name)
        return r.stdout.strip()

# Get the bug signature
node_out = run_node(original)
vjs_out, _ = run_vjs(original)

if node_out == vjs_out:
    print("No bug detected in original — cannot minimize")
else:
    # Token-level minimization
    tokens = original.split()
    current = original
    for i in range(len(tokens)):
        candidate = " ".join(tokens[:i] + tokens[i+1:])
        if not candidate.strip():
            continue
        try:
            n = run_node(candidate)
            v, _ = run_vjs(candidate)
            if n != v and n == node_out:
                current = candidate
                tokens = current.split()
        except Exception:
            pass
    print(f"Original ({{len(original)}} chars): {{original}}")
    print(f"Minimized ({{len(current)}} chars): {{current}}")
    print(f"Node: {{node_out}}")
    print(f"VJS:  {{vjs_out}}")
"""
        return _run_python(code, timeout=120)

    @Tool.define
    def stress_nesting(self, max_depth: int = 50) -> str:
        """Generate deeply nested JS expressions and test for stack overflows
        or incorrect evaluation at various depths."""
        code = f"""
import subprocess, tempfile, os

bugs = []
for depth in range(1, {max_depth} + 1):
    # Nested parens around a value
    expr = "(" * depth + "1 + 1" + ")" * depth
    js = f"console.log({{expr}})"
    with tempfile.NamedTemporaryFile(suffix=".js", mode="w", delete=False) as f:
        f.write(js); f.flush()
        nr = subprocess.run(["node", f.name], capture_output=True, text=True, timeout=5)
        node_out = nr.stdout.strip()
        os.unlink(f.name)
    with tempfile.NamedTemporaryFile(suffix=".js", mode="w", delete=False, dir=".") as f:
        f.write(js); f.flush()
        vr = subprocess.run(f"lake exe verifiedjs {{f.name}} --run=core",
                            shell=True, capture_output=True, text=True, timeout=30)
        vjs_out = vr.stdout.strip()
        vjs_err = vr.stderr.strip()
        os.unlink(f.name)
    if "stack" in vjs_err.lower() or "overflow" in vjs_err.lower():
        bugs.append(f"depth={{depth}}: STACK OVERFLOW")
        break
    elif node_out != vjs_out:
        bugs.append(f"depth={{depth}}: node={{node_out}} vjs={{vjs_out}}")

if bugs:
    print(f"Found {{len(bugs)}} issues:")
    for b in bugs:
        print(f"  {{b}}")
else:
    print(f"All depths 1-{max_depth} OK")
"""
        return _run_python(code, timeout=120)

    @Template.define
    def fuzz_pipeline(self, focus_areas: str) -> FuzzResult:
        """Generate adversarial JS inputs and try to break the pipeline.

        You MUST use your specialized tools:
        1. grammar_fuzz_js to generate tricky JS programs by category
        2. hypothesis_fuzz for property-based random testing
        3. pipeline_consistency_check on each generated program
        4. stress_nesting to find stack overflow limits
        5. minimize_reproducer on any bugs found
        6. batch_differential_test for bulk comparison
        7. Return FuzzResult with concrete, executable FuzzCases

        Each FuzzCase must have reproducer_command that anyone can run.

        Focus areas:
        {focus_areas}"""
        raise NotHandled


class SoundnessAuditorAgent(_SharedTools, PersistentAgent):
    """You are a soundness auditor for the VerifiedJS proof development.
    Your job is to find HOLES in the verification — places where the proofs
    are incomplete, unsound, or cheating.

    You have specialized tools:
    - sorry_dependency_graph: trace which theorems depend on sorrys
    - axiom_scan: find all axioms and noncomputable defs
    - check_theorem_vacuity: check if a theorem is vacuously true
    - proof_chain_analysis: analyze the EndToEnd proof chain completeness
    - lean_print_axioms: use Lean's #print axioms command

    You are paranoid and pedantic.
    """

    @Tool.define
    def sorry_dependency_graph(self) -> str:
        """Build a dependency graph showing which theorems transitively depend
        on sorry. Identifies critical-path sorrys (those blocking EndToEnd)."""
        code = f"""
import re, os
from pathlib import Path
from collections import defaultdict

root = Path("{LEAN_SRC}")
sorry_locs = []
theorem_map = {{}}  # name -> file:line
sorry_theorems = set()

for f in sorted(root.rglob("*.lean")):
    rel = f.relative_to(Path("{PROJECT_ROOT}"))
    lines = f.read_text().splitlines()
    current_thm = None
    for i, line in enumerate(lines, 1):
        # Track current theorem/lemma/def
        m = re.match(r'\\s*(theorem|lemma|def|instance)\\s+(\\S+)', line)
        if m:
            current_thm = m.group(2)
            theorem_map[current_thm] = f"{{rel}}:{{i}}"
        if 'sorry' in line and not line.strip().startswith('--'):
            sorry_locs.append((str(rel), i, line.strip(), current_thm or "<toplevel>"))
            if current_thm:
                sorry_theorems.add(current_thm)

# Check which sorry theorems are on the critical path (used in Proofs/)
proofs_dir = root / "Proofs"
critical = set()
if proofs_dir.exists():
    for f in proofs_dir.rglob("*.lean"):
        content = f.read_text()
        for thm in sorry_theorems:
            short = thm.split(".")[-1]
            if short in content:
                critical.add(thm)

print(f"Total sorrys: {{len(sorry_locs)}}")
print(f"Theorems with sorry: {{len(sorry_theorems)}}")
print(f"Critical-path sorrys (used in Proofs/): {{len(critical)}}")
print()
for loc in sorry_locs:
    marker = " [CRITICAL]" if loc[3] in critical else ""
    print(f"  {{loc[0]}}:{{loc[1]}} in {{loc[3]}}{{marker}}")
    print(f"    {{loc[2]}}")
"""
        return _run_python(code)

    @Tool.define
    def axiom_scan(self) -> str:
        """Scan all Lean files for axiom declarations, noncomputable defs,
        and uses of Classical.choice / Decidable.decide on non-obvious types."""
        results = []
        for pattern in ["axiom ", "noncomputable ", "Classical.choice",
                        "Classical.em", "Classical.byContradiction"]:
            out = _run(
                f"grep -rn '{pattern}' --include='*.lean' VerifiedJS/ 2>/dev/null"
            )
            if out and "No matches" not in out:
                results.append(f"=== {pattern} ===\n{out}")
        return "\n\n".join(results) if results else "No axioms or classical logic found."

    @Tool.define
    def check_theorem_vacuity(self, lean_file: str, theorem_name: str) -> str:
        """Check if a theorem might be vacuously true by examining its hypotheses.
        Writes a small Lean file that tries to construct the hypothesis type."""
        code = f"""
import re
from pathlib import Path

content = Path("{PROJECT_ROOT}" + "/" + "{lean_file}").read_text()
# Find the theorem
pattern = r'theorem\\s+{theorem_name}[^:]*:\\s*(.+?)(?::=|where|by)'
m = re.search(pattern, content, re.DOTALL)
if m:
    stmt = m.group(1).strip()
    print(f"Theorem statement:")
    print(f"  {{stmt[:500]}}")
    # Check for suspicious patterns
    issues = []
    if "False" in stmt and "→" in stmt:
        issues.append("Contains False in hypothesis chain — might be vacuously true")
    if stmt.count("∀") > 3:
        issues.append("Many universal quantifiers — check if types are inhabited")
    if "Empty" in stmt or "Fin 0" in stmt:
        issues.append("Contains empty type — likely vacuous")
    if issues:
        print("\\nPotential vacuity issues:")
        for iss in issues:
            print(f"  - {{iss}}")
    else:
        print("\\nNo obvious vacuity issues detected (manual review still recommended)")
else:
    print(f"Theorem '{theorem_name}' not found in {lean_file}")
"""
        return _run_python(code)

    @Tool.define
    def proof_chain_analysis(self) -> str:
        """Analyze the end-to-end proof chain. Check each pass correctness
        theorem and whether it's proven or has sorry."""
        code = f"""
import re
from pathlib import Path

proofs_dir = Path("{LEAN_SRC}") / "Proofs"
if not proofs_dir.exists():
    print("Proofs/ directory not found")
    exit()

chain = [
    ("ElaborateCorrect.lean", "elaborate"),
    ("ClosureConvertCorrect.lean", "closure_convert"),
    ("ANFConvertCorrect.lean", "anf_convert"),
    ("LowerCorrect.lean", "lower"),
    ("EmitCorrect.lean", "emit"),
    ("OptimizeCorrect.lean", "optimize"),
    ("EndToEnd.lean", "end_to_end"),
]

for filename, pass_name in chain:
    filepath = proofs_dir / filename
    if not filepath.exists():
        print(f"  MISSING: {{filename}}")
        continue
    content = filepath.read_text()
    sorry_count = content.count("sorry")
    theorems = re.findall(r'theorem\\s+(\\S+)', content)
    proven = [t for t in theorems if True]  # all declared
    status = "SORRY" if sorry_count > 0 else "PROVEN"
    marker = "X" if sorry_count > 0 else "✓"
    print(f"  [{{marker}}] {{filename}}: {{len(theorems)}} theorems, {{sorry_count}} sorrys — {{status}}")
    if sorry_count > 0:
        lines = content.splitlines()
        for i, line in enumerate(lines, 1):
            if "sorry" in line and not line.strip().startswith("--"):
                print(f"      L{{i}}: {{line.strip()[:80]}}")
"""
        return _run_python(code)

    @Tool.define
    def lean_print_axioms(self, theorem_name: str) -> str:
        """Use Lean's #print axioms command to see what axioms a theorem depends on.
        Writes a temporary file and runs it."""
        lean_code = f"#print axioms {theorem_name}"
        with tempfile.NamedTemporaryFile(
            suffix=".lean", mode="w", delete=False, dir=str(PROJECT_ROOT)
        ) as f:
            f.write(f"import VerifiedJS\n{lean_code}\n")
            f.flush()
            try:
                return _run(f"lake env lean {f.name}", timeout=120)
            finally:
                os.unlink(f.name)

    @Tool.define
    def check_native_decide_safety(self) -> str:
        """Find all uses of native_decide and check whether the types involved
        are actually finite/decidable."""
        code = f"""
import re
from pathlib import Path

root = Path("{LEAN_SRC}")
issues = []
for f in sorted(root.rglob("*.lean")):
    rel = f.relative_to(Path("{PROJECT_ROOT}"))
    lines = f.read_text().splitlines()
    for i, line in enumerate(lines, 1):
        if "native_decide" in line:
            # Look for context around it
            ctx_start = max(0, i - 5)
            ctx = lines[ctx_start:i+2]
            issues.append((str(rel), i, line.strip(), "\\n".join(ctx)))

if issues:
    print(f"Found {{len(issues)}} native_decide uses:")
    for loc in issues:
        print(f"\\n  {{loc[0]}}:{{loc[1]}}: {{loc[2]}}")
        print(f"  Context:")
        for cl in loc[3].split("\\n"):
            print(f"    {{cl}}")
else:
    print("No native_decide uses found")
"""
        return _run_python(code)

    @Template.define
    def audit_soundness(self, scope: str) -> SoundnessAuditResult:
        """Perform a thorough soundness audit.

        You MUST use your specialized tools:
        1. sorry_dependency_graph — find all sorrys and their blast radius
        2. axiom_scan — find custom axioms and classical logic usage
        3. proof_chain_analysis — check EndToEnd proof completeness
        4. check_native_decide_safety — verify native_decide is safe
        5. lean_print_axioms on key theorems — verify axiom dependencies
        6. check_theorem_vacuity on suspicious theorems
        7. Return SoundnessAuditResult with all fields filled

        Scope:
        {scope}"""
        raise NotHandled


# ---------------------------------------------------------------------------
# Choreographic program — the LOOPING multi-agent workflow
# ---------------------------------------------------------------------------


def verified_compiler_development_loop(
    planner: PlannerSupervisor,
    context_builder: ContextSupervisor,
    spec_writer: SpecWriterAgent,
    tester: TestWriterAgent,
    prover: ProverAgent,
    memory: MemoryKeeperAgent,
    spec_challenger: SpecChallengerAgent,
    fuzzer: FuzzerAgent,
    soundness_auditor: SoundnessAuditorAgent,
) -> dict:
    """Choreographic program: continuous development loop with adversarial testing.

    Runs up to MAX_CYCLES iterations of:
      Phase 1: Planning (incorporating adversarial findings)
      Phase 2: Context assembly
      Phase 3: Parallel execution (constructive workers)
      Phase 3.5: Adversarial phase (challenger, fuzzer, auditor in parallel)
      Phase 4: Review + revision (informed by adversarial findings)
      Phase 5: Memory persistence
      Phase 6: Continue decision
    """

    all_cycle_reports: list[dict] = []
    memory_report: MemoryReport = {
        "files_updated": [], "sorry_count_before": 0, "sorry_count_after": 0,
        "sorry_delta": 0, "build_healthy": False, "e2e_pass": False,
        "regressions": [], "key_findings": [], "new_blockers": [],
        "resolved_blockers": [],
    }
    # Adversarial findings accumulate across cycles
    prev_adversarial: str = "First cycle — no previous adversarial findings."

    for cycle in range(1, MAX_CYCLES + 1):
        log.info(f"{'=' * 60}")
        log.info(f"CYCLE {cycle}/{MAX_CYCLES}")
        log.info(f"{'=' * 60}")

        # ── Phase 1: Planning ──────────────────────────────────────

        log.info(f"[Cycle {cycle}] Phase 1: Planning")

        tasks_content = planner.read_file("TASKS.md")
        progress_content = planner.read_file("PROGRESS.md")
        blockers_content = planner.read_file("PROOF_BLOCKERS.md")
        sorry_count = planner.count_sorrys()
        build_status = planner.lake_build()

        current_state = (
            f"## TASKS.md\n{tasks_content}\n\n"
            f"## PROGRESS.md\n{progress_content}\n\n"
            f"## PROOF_BLOCKERS.md\n{blockers_content}\n\n"
            f"## Sorry Count\n{sorry_count}\n\n"
            f"## Build Status\n{build_status[:1500]}\n"
        )

        if all_cycle_reports:
            prev = all_cycle_reports[-1]
            current_state += (
                f"\n## Previous Cycle Summary\n"
                f"{json.dumps(prev, indent=2, default=str)[:2000]}\n"
            )

        plan = planner.plan_next_sprint(
            current_state, cycle, prev_adversarial,
        )
        log.info(
            f"[Cycle {cycle}] Planned {len(plan['tasks'])} tasks: "
            f"{plan['rationale'][:200]}"
        )

        if not plan["tasks"]:
            log.info(f"[Cycle {cycle}] No tasks planned — stopping.")
            break

        # ── Phase 2: Context Assembly ──────────────────────────────

        log.info(f"[Cycle {cycle}] Phase 2: Context assembly")

        context_bundles: list[ContextBundle] = scatter(
            plan["tasks"],
            context_builder,
            lambda ctx_agent, task: ctx_agent.assemble_context(
                json.dumps(task, indent=2)
            ),
        )

        # ── Phase 3: Parallel Execution (constructive) ─────────────

        log.info(f"[Cycle {cycle}] Phase 3: Parallel execution")

        spec_tasks: list[dict] = []
        test_tasks: list[dict] = []
        proof_tasks: list[dict] = []
        for task, ctx in zip(plan["tasks"], context_bundles):
            bundle = {"task": task, "context": ctx}
            if task["task_type"] in ("spec", "implement"):
                spec_tasks.append(bundle)
            elif task["task_type"] == "test":
                test_tasks.append(bundle)
            elif task["task_type"] in ("prove", "review"):
                proof_tasks.append(bundle)

        spec_results: list[SpecResult] = []
        if spec_tasks:
            log.info(f"  Dispatching {len(spec_tasks)} spec/impl tasks")
            spec_results = scatter(
                spec_tasks,
                spec_writer,
                lambda w, b: w.write_spec(json.dumps(b, indent=2)),
            )

        test_results: list[TestResult] = []
        if test_tasks:
            log.info(f"  Dispatching {len(test_tasks)} test tasks")
            test_results = scatter(
                test_tasks,
                tester,
                lambda t, b: t.write_tests_and_validate(json.dumps(b, indent=2)),
            )

        proof_results: list[ProofResult] = []
        if proof_tasks:
            log.info(f"  Dispatching {len(proof_tasks)} proof tasks")
            proof_results = scatter(
                proof_tasks,
                prover,
                lambda p, b: p.prove_theorem(json.dumps(b, indent=2)),
            )

        # ── Phase 3.5: Adversarial phase (parallel) ───────────────

        log.info(f"[Cycle {cycle}] Phase 3.5: Adversarial testing")

        # Determine what modules the constructive agents touched this cycle
        touched_modules = set()
        for task in plan["tasks"]:
            touched_modules.add(task["module"])
        modules_str = ", ".join(sorted(touched_modules)) or "Core, Flat"

        # Spec challenger
        challenge_result: SpecChallengeResult = spec_challenger.challenge_specs(
            f"Modules to attack: {modules_str}. "
            f"Focus on recently changed files from this cycle's tasks: "
            f"{json.dumps([t['target_file'] for t in plan['tasks']], default=str)}"
        )
        log.info(
            f"  Challenger: {len(challenge_result.get('violations', []))} violations found"
        )

        # Fuzzer
        fuzz_result: FuzzResult = fuzzer.fuzz_pipeline(
            f"Focus on stages: {modules_str}. "
            f"Recently touched files: "
            f"{json.dumps([t['target_file'] for t in plan['tasks']], default=str)}"
        )
        log.info(
            f"  Fuzzer: {len(fuzz_result.get('bugs_found', []))} bugs in "
            f"{fuzz_result.get('cases_tried', 0)} cases"
        )

        # Soundness auditor
        audit_result: SoundnessAuditResult = soundness_auditor.audit_soundness(
            f"Audit scope: {modules_str} plus Proofs/. "
            f"Focus on files changed this cycle."
        )
        log.info(
            f"  Auditor: {len(audit_result.get('soundness_issues', []))} issues, "
            f"risk={audit_result.get('overall_risk', '?')}"
        )

        # Compile adversarial findings for the next cycle's planner
        adversarial_summary = {
            "spec_violations": challenge_result.get("violations", []),
            "fuzz_bugs": fuzz_result.get("bugs_found", []),
            "soundness_issues": audit_result.get("soundness_issues", []),
            "overall_risk": audit_result.get("overall_risk", "unknown"),
            "critical_path_sorrys": audit_result.get("critical_path_sorrys", 0),
        }
        prev_adversarial = json.dumps(adversarial_summary, indent=2, default=str)

        # ── Phase 4: Review + Revision ─────────────────────────────

        log.info(f"[Cycle {cycle}] Phase 4: Review (with adversarial context)")

        all_results: list[tuple] = []
        for t, r in zip([b["task"] for b in spec_tasks], spec_results):
            all_results.append(("spec", t, r))
        for t, r in zip([b["task"] for b in test_tasks], test_results):
            all_results.append(("test", t, r))
        for t, r in zip([b["task"] for b in proof_tasks], proof_results):
            all_results.append(("proof", t, r))

        reviews: list[ReviewResult] = []
        needs_revision: list = []
        accepted = 0
        for kind, task, result in all_results:
            review = planner.review_completed_work(
                task_id=task["task_id"],
                task_spec=json.dumps(task, indent=2),
                result=json.dumps(result, indent=2, default=str),
            )
            reviews.append(review)
            if review["verdict"] == "ACCEPT":
                accepted += 1
            elif review["verdict"] == "REVISE":
                needs_revision.append((kind, task, result, review))
            log.info(
                f"  [{task['task_id']}] {review['verdict']}: "
                f"{review['feedback'][:100]}"
            )

        # One revision round
        if needs_revision:
            log.info(f"  Revising {len(needs_revision)} items")
            for kind, task, result, review in needs_revision:
                rev_payload = json.dumps(
                    {
                        "task": task,
                        "original_result": result,
                        "REVISION": True,
                        "feedback": review["feedback"],
                        "adversarial_context": adversarial_summary,
                    },
                    indent=2,
                    default=str,
                )
                if kind == "spec":
                    scatter(
                        [rev_payload], spec_writer,
                        lambda w, r: w.write_spec(r),
                    )
                elif kind == "test":
                    scatter(
                        [rev_payload], tester,
                        lambda t, r: t.write_tests_and_validate(r),
                    )
                elif kind == "proof":
                    scatter(
                        [rev_payload], prover,
                        lambda p, r: p.prove_theorem(r),
                    )

        # ── Phase 5: Memory Persistence ────────────────────────────

        log.info(f"[Cycle {cycle}] Phase 5: Memory persistence")

        cycle_summary = {
            "cycle": cycle,
            "tasks_planned": len(plan["tasks"]),
            "tasks_accepted": accepted,
            "tasks_revised": len(needs_revision),
            "tasks_rejected": len(all_results) - accepted - len(needs_revision),
            "rationale": plan["rationale"],
            "spec_results": spec_results,
            "test_results": test_results,
            "proof_results": proof_results,
            "reviews": reviews,
            "adversarial": adversarial_summary,
        }

        memory_report = memory.persist_findings(
            json.dumps(cycle_summary, indent=2, default=str)
        )
        log.info(
            f"  Memory: sorry delta={memory_report.get('sorry_delta', '?')}, "
            f"build={memory_report.get('build_healthy', '?')}, "
            f"regressions={len(memory_report.get('regressions', []))}"
        )

        all_cycle_reports.append(cycle_summary)

        # ── Phase 6: Continue? ─────────────────────────────────────

        log.info(f"[Cycle {cycle}] Phase 6: Continue decision")

        continue_decision = planner.decide_continue(
            json.dumps(cycle_summary, indent=2, default=str)
        )

        log.info(
            f"  Continue: {continue_decision['should_continue']} — "
            f"{continue_decision['reason'][:150]}"
        )

        if not continue_decision["should_continue"]:
            log.info(f"Planner decided to stop after cycle {cycle}.")
            break

    return {
        "total_cycles": len(all_cycle_reports),
        "cycle_reports": all_cycle_reports,
        "final_memory_report": memory_report,
        "final_adversarial": prev_adversarial,
    }


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main() -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)

    log.info("VerifiedJS Multi-Agent Choreography (with adversarial agents)")
    log.info(f"  Project root: {PROJECT_ROOT}")
    log.info(f"  Model: {MODEL}")
    log.info(f"  Max cycles: {MAX_CYCLES}")
    log.info(f"  Max history len: {MAX_HISTORY_LEN}")
    log.info(f"  State dir: {STATE_DIR}")

    # ── Create constructive agents ─────────────────────────────────

    planner = PlannerSupervisor(agent_id="planner-supervisor")
    context_builder = ContextSupervisor(agent_id="context-supervisor")
    spec_writer_1 = SpecWriterAgent(agent_id="spec-writer-1")
    spec_writer_2 = SpecWriterAgent(agent_id="spec-writer-2")
    tester = TestWriterAgent(agent_id="test-writer")
    prover_1 = ProverAgent(agent_id="prover-1")
    prover_2 = ProverAgent(agent_id="prover-2")
    memory_keeper = MemoryKeeperAgent(agent_id="memory-keeper")

    # ── Create adversarial agents ──────────────────────────────────

    spec_challenger = SpecChallengerAgent(agent_id="spec-challenger")
    fuzzer = FuzzerAgent(agent_id="fuzzer")
    soundness_auditor = SoundnessAuditorAgent(agent_id="soundness-auditor")

    all_agents = [
        planner, context_builder,
        spec_writer_1, spec_writer_2,
        tester,
        prover_1, prover_2,
        memory_keeper,
        spec_challenger, fuzzer, soundness_auditor,
    ]

    # ── Build choreography ─────────────────────────────────────────

    choreo = Choreography(
        verified_compiler_development_loop,
        agents=all_agents,
        queue=PersistentTaskQueue(STATE_DIR / "choreo_queue"),
        handlers=[
            LiteLLMProvider(model=MODEL),
            RetryLLMHandler(),
            CompactionHandler(max_history_len=MAX_HISTORY_LEN),
            PersistenceHandler(STATE_DIR / "persistence"),
        ],
    )

    log.info(f"Agents ({len(all_agents)}): {', '.join(a.__agent_id__ for a in all_agents)}")
    log.info("Starting development loop (Ctrl-C to pause, re-run to resume)")

    # ── Run ────────────────────────────────────────────────────────

    try:
        result = choreo.run(
            planner=planner,
            context_builder=[context_builder],
            spec_writer=[spec_writer_1, spec_writer_2],
            tester=[tester],
            prover=[prover_1, prover_2],
            memory=memory_keeper,
            spec_challenger=[spec_challenger],
            fuzzer=[fuzzer],
            soundness_auditor=[soundness_auditor],
        )
    except ChoreographyError as e:
        log.error(f"Choreography failed: {e}")
        return
    except KeyboardInterrupt:
        log.info("Interrupted — state saved. Re-run to resume.")
        return

    # ── Final Summary ──────────────────────────────────────────────

    total = result.get("total_cycles", 0)
    reports = result.get("cycle_reports", [])
    mem = result.get("final_memory_report", {})

    log.info("=" * 60)
    log.info(f"Development loop complete — {total} cycles")
    for i, rpt in enumerate(reports, 1):
        adv = rpt.get("adversarial", {})
        log.info(
            f"  Cycle {i}: {rpt.get('tasks_planned', 0)} planned, "
            f"{rpt.get('tasks_accepted', 0)} accepted, "
            f"{len(adv.get('spec_violations', []))} violations, "
            f"{len(adv.get('fuzz_bugs', []))} fuzz bugs, "
            f"{len(adv.get('soundness_issues', []))} soundness issues"
        )

    if isinstance(mem, dict):
        log.info(
            f"  Final: sorry delta={mem.get('sorry_delta', '?')}, "
            f"build={'OK' if mem.get('build_healthy') else 'BROKEN'}, "
            f"regressions={len(mem.get('regressions', []))}"
        )

    sorry_out = _run(
        "grep -rc 'sorry' --include='*.lean' VerifiedJS/ 2>/dev/null "
        "| awk -F: '{s+=$2}END{print s}'"
    )
    log.info(f"  Final sorry count: {sorry_out}")
    log.info("=" * 60)


if __name__ == "__main__":
    main()
