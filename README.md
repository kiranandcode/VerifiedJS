# VerifiedJS: A Formally Verified JavaScript-to-WebAssembly Compiler in Lean 4

This file is the agent operating prompt (formerly `AGENT_PROMPT.md`).
    
## Mission

Build a formally verified compiler from **full JavaScript** (ECMAScript 2020) to WebAssembly, written entirely in Lean 4. The compiler's correctness—semantic preservation from source to target—is proved mechanically in Lean's type theory. The compiled output runs on any standard Wasm runtime. End-to-end behavior is validated against Node.js using Test262.

### Normative Reference

The **ECMAScript 2020 Language Specification** is the normative reference for all semantic decisions:

> **https://tc39.es/ecma262/2020/**

Every agent implementing or formalizing JS semantics must cite the specific section of this spec justifying the behavior. For example, when implementing `ToNumber`, cite §7.1.3. When implementing `[[Get]]`, cite §9.1.8. When formalizing evaluation order, cite §12.

Lean docstrings on semantic rules should include the spec section number:

```lean
/-- ECMA-262 §13.15.2 Runtime Semantics: Evaluation — AssignmentExpression -/
inductive AssignmentEval : ... → Prop where
```

When the spec is ambiguous, document the ambiguity in `ARCHITECTURE.md` and pick the behavior that matches Node.js (v20 LTS).

### The Flagship Target

The compiler's "Linux kernel moment" is **compiling the TypeScript compiler (`tsc`) to WebAssembly and using it to typecheck real TypeScript projects**. `tsc` is ~130,000 lines of JavaScript, exercises every corner of the language, and is the single most widely-used JS tool in the world. When VerifiedJS can compile `tsc` to `.wasm` and that `.wasm` can typecheck a real TypeScript codebase producing identical diagnostics to `node ./tsc.js`, the compiler is done.

Secondary targets (in rough order of difficulty):

1. **Prettier** (~50k LOC) — format JS/TS files, diff output against native Prettier
2. **Babel** (~70k LOC) — transpile modern JS, compare output against native Babel
3. **Three.js examples** — compile a Three.js demo, render in a browser via Wasm
4. **TypeScript compiler** (~130k LOC) — the flagship

The flagship repos are tracked as git submodules under `tests/flagship/`:
- `tests/flagship/prettier`
- `tests/flagship/babel`
- `tests/flagship/TypeScript`

---

## Architecture (CompCert-Derived)

The compiler is a pipeline of formally verified passes. Each pass transforms between two intermediate languages and is equipped with a Lean proof of semantic preservation (a forward simulation). Composition yields end-to-end correctness.

There is **no optimization pass**. A verified compiler is the goal. A stub module (`Optimize.lean`) exists where optimizations can be added later; each future optimization must carry its own simulation proof.

### Compilation Pipeline

```
JavaScript source
  │
  ├─ [1] Lexing + Parsing (outside TCB; validated by test suite)
  ▼
JS.AST                    ← full ECMAScript 2020 abstract syntax
  │
  ├─ [2] Elaboration + desugaring
  ▼
JS.Core                   ← normalized core: destructuring/for-in/classes → primitives
  │
  ├─ [3] Closure conversion + environment representation
  ▼
JS.Flat                   ← first-order; closures → structs + function indices
  │
  ├─ [4] ANF conversion (side effects sequenced, all subexpressions named)
  ▼
JS.ANF                    ← A-normal form
  │
  ├─ [5] [STUB] Optimization passes (no-op identity for now)
  ▼
JS.ANF                    ← unchanged
  │
  ├─ [6] Lowering to Wasm IR
  ▼
Wasm.IR                   ← structured control flow, Wasm types, linear memory ops
  │
  ├─ [7] Wasm IR → Wasm AST
  ▼
Wasm.AST                  ← abstract Wasm module (mirrors WasmCert-Coq)
  │
  ├─ [8] Binary encoding (outside TCB; validated by wasm-tools + Valex-style checker)
  ▼
.wasm binary
```

### Every IL Is Inspectable

Each intermediate language has four components that must exist before the pass is considered complete:

1. **`Syntax.lean`** — inductive type definitions
2. **`Semantics.lean`** — small-step LTS as an inductive relation `Step : State → Trace → State → Prop`
3. **`Interp.lean`** — executable reference interpreter (`def interp : Program → IO (List Trace)`)
4. **`Print.lean`** — pretty-printer producing human-readable output

The CLI exposes each IL:

```bash
lake exe verifiedjs input.js --emit=core    # print JS.Core
lake exe verifiedjs input.js --emit=flat    # print JS.Flat
lake exe verifiedjs input.js --emit=anf     # print JS.ANF
lake exe verifiedjs input.js --emit=wasmIR  # print Wasm.IR
lake exe verifiedjs input.js --emit=wat     # print Wasm text format
lake exe verifiedjs input.js --run=core     # interpret at JS.Core level
lake exe verifiedjs input.js --run=anf      # interpret at JS.ANF level
lake exe verifiedjs input.js --run=wasmIR   # interpret at Wasm.IR level
```

This is essential for debugging. When an end-to-end test fails, agents bisect by running interpreters at each level to isolate which pass introduced the bug.

---

## Semantic Preservation

For each pass `P : IL_in → IL_out`, prove:

```lean
theorem P_correct (s : IL_in.Program) (t : IL_out.Program) (h : P s = some t) :
    ∀ b, IL_out.Behaves t b → ∃ b', IL_in.Behaves s b' ∧ BehaviorRefines b b'
```

JavaScript has no undefined behavior (unlike C), so `BehaviorRefines` is exact equality on defined programs. Compose all pass theorems in `EndToEnd.lean`.

### Optimization Stub

```lean
-- VerifiedJS/ANF/Optimize.lean
/-- Identity pass. Future optimizations go here, each with a simulation proof. -/
def optimize (p : ANF.Program) : ANF.Program := p

theorem optimize_correct (p : ANF.Program) :
    ∀ b, ANF.Behaves (optimize p) b ↔ ANF.Behaves p b := by
  intro b; constructor <;> (intro h; exact h)
```

---

## Wasm Target Semantics

Port the relevant subset of WasmCert-Coq's Rocq formalization to Lean 4:

- `Wasm.Syntax` — module structure, instructions, types (from WasmCert-Coq `theories/datatypes.v`)
- `Wasm.Validation` — type checking rules
- `Wasm.Execution` — small-step reduction, store, stack, frames
- `Wasm.Numerics` — i32/i64/f32/f64 operations

Reference repos:
- **WasmCert-Coq** (`github.com/WasmCert/WasmCert-Coq`): canonical Rocq formalization of Wasm 2.0
- **lean-wasm** (`github.com/T-Brick/lean-wasm`): existing Lean 4 Wasm formalization

Target Wasm 1.0 MVP + bulk memory + mutable globals.

---

## Parser / Lexer

JS lexing is context-sensitive (`/` is division or regex depending on prior token). Hand-written lexer producing a `Token` stream. Recursive descent parser — JS grammar is not LR(1).

The parser is **outside the verified TCB**. Validate by:
- Test262 parse-only tests
- Round-trip: `parse ∘ print ≈ id` on the AST
- Differential: parse with VerifiedJS, parse with Acorn/Babel, compare ASTs
- Fail-fast flagship parser gate (benchmark-first, project-by-project smoke): run `./scripts/parse_flagship_failfast.sh --project prettier --sample-per-project 200`, then `--project babel --sample-per-project 200`, then `--project TypeScript --sample-per-project 200`
- Completion gate: `./scripts/parse_flagship_failfast.sh --full` (all flagship JS files)
- Long-sequence integration sweep: `./scripts/parse_flagship.sh --full --integration-only`

Reference: `argumentcomputer/Wasm.lean` uses Megaparsec.lean for WAST parsing.

---

## Runtime / Memory Model

- **Value representation**: NaN-boxing in f64, or tagged pointers in i64
- **Heap**: bump allocator + mark-sweep GC compiled into the Wasm module
- **Strings**: interned, UTF-16, stored in linear memory
- **Objects**: property maps as linked hash tables in linear memory
- **Closures**: `(function_index, environment_pointer)` pairs
- **Prototypes**: chain traversal in linear memory
- **Generators/async**: CPS transform in JS.Flat, state machines in Wasm.IR
- **Proxies**: trap table indirection
- **WeakMap/WeakSet**: weak reference table integrated with GC
- **Regex**: DFA/NFA engine in the runtime

The runtime is linked into every output module. Its semantics are axiomatic—document the TCB boundary in `ARCHITECTURE.md`.

---

## Language Server Integration

Every Codex subagent workspace runs the **Lean LSP** and the **lean-lsp-mcp** MCP server (`github.com/oOo0oOo/lean-lsp-mcp`). Agents use LSP feedback as a primary signal, not just `lake build` exit codes.

### Setup (per subagent workspace)

```bash
pip install leanclient --break-system-packages
codex mcp add lean-lsp -s project uvx lean-lsp-mcp
```

### Agent Workflow with LSP

1. **Before editing**: query `lean_file_diagnostics` on the target file.
2. **After editing**: save, wait for re-elaboration, query diagnostics again. Fix new errors before committing.
3. **For proofs**: use `lean_goal` to inspect proof state at a specific line/column.
4. **For exploration**: use `lean_hover` for types, `lean_completions` for lemmas.
5. **For search**: use `lean_search` (LeanSearch), `lean_loogle` (Loogle), `lean_local_search` (ripgrep).

---

## Iterative Verified Design

Verified code development is a loop:

```
define interface/types → write implementation → attempt proof →
  ├─ proof succeeds → done
  └─ proof fails →
       ├─ adjust implementation to make it more provable → retry
       ├─ refine the theorem statement → retry
       └─ restructure the IL definition → retry (coordinate via ARCHITECTURE.md)
```
### Phase 0: Parser and AST codesign

Based on the ECMAScript specification, write a parser for javascript using the lean  parsing library. Iterate on this parser and the AST until we can parse ALL benchmarks, and pretty-print them to equivalent ASTs. This phase is somewhat independent of the proof steps that come later.

### Phase 1: Interface Consensus

Before any implementation, define:
- All IL `Syntax.lean` types (inductive definitions)
- All pass function signatures (input/output types)
- All correctness theorem statements (type signatures with `sorry` bodies)
- All `Semantics.lean` relation signatures

These go directly into the module files as `sorry`'d stubs. This is the contract that enables parallel work.

### Phase 2: Parallel Extension

Once interfaces are agreed, agents pull tasks greedily (see Agent Structure below). Example parallel work streams on a single IL:
- Implement the pass itself
- Implement the interpreter
- Implement the pretty-printer
- Write unit tests
- Begin the correctness proof (using `sorry` for lemmas depending on unfinished implementation)

### Phase 3: Proof Convergence

Implementation and proofs co-evolve. When stuck:
1. Try automation first (see Proof Automation below)
2. Break the goal into lemmas, sorry each, try automation on each
3. If stuck >30 minutes on a single goal, file in `PROOF_BLOCKERS.md` with the goal state
4. If a property has been attempted 3+ times and failed, flag it in `PROOF_BLOCKERS.md` with `ESCALATE:` prefix. It may be false or the implementation may need restructuring.

---

## Sorry Management

`sorry` is a coordination mechanism. Unchecked proliferation defeats verification.

### Sorry Tracking Script

```bash
#!/bin/bash
# scripts/sorry_report.sh
echo "# Sorry Report ($(date))" > SORRY_REPORT.md
echo "" >> SORRY_REPORT.md

grep -rn "sorry" --include="*.lean" VerifiedJS/ | \
  grep -v "-- sorry OK:" | \
  grep -v "sorry_report" | \
  while IFS=: read -r file line content; do
    name=$(head -n "$line" "$file" | grep -oP '(theorem|lemma|def)\s+\K\S+' | tail -1)
    echo "- [ ] \`$file:$line\` — \`$name\` — \`$(echo "$content" | xargs)\`" >> SORRY_REPORT.md
  done

COUNT=$(grep -c "^\- \[" SORRY_REPORT.md || true)
echo "" >> SORRY_REPORT.md
echo "**Total: $COUNT sorries**" >> SORRY_REPORT.md

if [ "$COUNT" -gt 50 ]; then
  echo "ERROR: sorry count ($COUNT) exceeds threshold (50)"
  exit 1
fi
```

### Sorry Rules

1. Every sorry must have a `-- TODO:` comment explaining what remains.
2. Sorrys in `Proofs/` are expected during development. Sorrys in `Syntax.lean` or `Semantics.lean` are bugs.
3. Sorry count tracked in CI. Threshold: 100 → 50 → 20 → 0.
4. When closing a sorry, add `-- PROVED: <date>`.
5. Sorrys must not appear in `EndToEnd.lean` after Phase 2.

---

## Proof Automation Strategy

Maximize automation. Manual proof terms are a last resort.

### Tactic Priority (try in this order)

1. **`decide`** — decidable propositions
2. **`simp [lemma₁, lemma₂]`** — rewriting
3. **`omega`** — linear arithmetic over `Nat`, `Int`
4. **`grind`** — congruence closure + case splitting
5. **`canonical`** — type inhabitation solver (`github.com/chasenorman/Canonical`)
6. **`aesop`** — automated reasoning with custom rule sets
7. **`native_decide`** — kernel evaluation for large finite checks

### Proof Development Loop

```
goal appears
  │
  ├─ try decide / simp / omega / grind → closes goal → done
  │
  ├─ partial progress (subgoals remain):
  │    └─ continue, try automation on each subgoal
  │
  ├─ no progress:
  │    ├─ constructor / intro / cases / induction to decompose
  │    ├─ try automation on each branch
  │    └─ still stuck → break into lemma, sorry it, move on
  │
  └─ goal looks false:
       └─ flag ESCALATE in PROOF_BLOCKERS.md. Do NOT sorry a false statement.
```

### Custom Simp Sets

```lean
attribute [simp] JS.Core.eval_let JS.Core.eval_if JS.Core.eval_call
attribute [simp] Wasm.step_block Wasm.step_loop Wasm.step_br
```

### Dependencies

```lean
require Canonical from git "https://github.com/chasenorman/CanonicalLean" @ "main"
```

---

## Agent Team Structure

### No Fixed Roles — Greedy Task Pulling

Agents are **stateless and interchangeable**. Each agent is spawned fresh, uses a dedicated `git worktree`, reads the coordination files, picks the highest-priority unclaimed task, does it, pushes, and exits. A new agent is spawned immediately. There are no permanent role assignments.

This matches Anthropic's finding that their C compiler agents worked best without an orchestration agent—each simply picked up "the next most obvious problem."

### Harness

```bash
#!/bin/bash
# Each coordinator process runs this loop.
# Agents are spawned fresh, do one task, push, and exit.
# The loop respawns a new agent immediately.
while true; do
    cd /workspace || exit 1
    git fetch origin main

    WORKTREE=".worktrees/agent_$(date +%s)"
    BRANCH="codex/agent_${RANDOM}_$(date +%s)"
    git worktree add -b "$BRANCH" "$WORKTREE" origin/main || continue

    COMMIT=$(git -C "$WORKTREE" rev-parse --short=6 HEAD)
    LOGFILE="agent_logs/agent_${COMMIT}_$(date +%s).log"

    # Spawn a Codex subagent bound to the worktree.
    # The subagent reads README.md, picks a task, executes, then exits.
    codex run \
           -C "$WORKTREE" \
           -p "$(cat README.md)" \
           --mcp-config "$WORKTREE/.mcp.json" \
           &> "$LOGFILE"

    git -C "$WORKTREE" push -u origin "$BRANCH" || true
    git worktree remove "$WORKTREE" --force
    git branch -D "$BRANCH" 2>/dev/null || true
done
```

### Task Coordination

All work is driven by three coordination files. Agents read these on startup and pick greedily.

**`TASKS.md`** — the master task list. Maintained by all agents. Format:

```markdown
## Priority 1 (blocking)
- [ ] Define JS.Core.Syntax.lean inductive types — SPEC: §13, §14
- [ ] Implement JS.AST parser for IfStatement — SPEC: §13.6
- [x] Define Wasm.Syntax.lean module type — DONE by agent-3a2f

## Priority 2 (important)
- [ ] Write Interp.lean for JS.Core
- [ ] Pretty-printer for JS.Flat
- [ ] Unit tests for Elaborate pass

## Priority 3 (proof work)
- [ ] Prove ElaborateCorrect.lean — depends on: JS.Core.Semantics, Elaborate.lean
- [ ] Close sorry in ClosureConvertCorrect.lean:42

## Priority 4 (quality / review)
- [ ] Deduplicate helper functions in Wasm/ modules
- [ ] Update ARCHITECTURE.md to reflect new IR.lean structure
- [ ] Review and coalesce any reimplemented utility code
```

**`PROOF_BLOCKERS.md`** — goals agents are stuck on. Agents check this before starting proof work to avoid duplicating failed attempts.

**`PROGRESS.md`** — per-pass status. Updated by every agent before pushing.

When agents discover missing prerequisite work, regressions, or follow-up tasks while implementing, they must add new unchecked items to `TASKS.md` immediately (with priority + short rationale/dependency note), then continue or hand off.

### Agent Startup Protocol

Every agent, on every spawn, does this:

1. `git fetch origin main && git worktree add -b codex/<task-id> .worktrees/<task-id> origin/main`
2. Read `TASKS.md`. Find the highest-priority unchecked task that is not locked in `current_tasks/`.
3. `cd` into that worktree and lock the task: `echo "$(date): <description>" > current_tasks/<task_name>.txt && git add && git commit && git push`. If push fails (another agent claimed it), remove the worktree and go back to step 1.
4. Read `ARCHITECTURE.md` to understand the current state.
5. Read `PROGRESS.md` to understand what's done and what's in flight.
6. If the task is proof work, read `PROOF_BLOCKERS.md` to avoid repeating failed attempts.
7. Do the task. Run `./tests/run_tests.sh --fast` before pushing. If the task touches parser/lexer/AST, also run project-by-project parser smoke gates with `./scripts/parse_flagship_failfast.sh --project prettier --sample-per-project 200`, then `--project babel --sample-per-project 200`, then `--project TypeScript --sample-per-project 200` (and `--full` when validating parser completion/regression fixes).
8. Update `TASKS.md` (mark done), `PROGRESS.md` (update status), and `SORRY_REPORT.md` (run script).
   If the task revealed additional required work, append those new tasks to `TASKS.md` before exiting.
9. Remove lock. Push. Clean up worktree (`git worktree remove`). Exit.

### Task Types (any agent can do any of these)

| Type | Description |
|---|---|
| **interface** | Define Syntax/Semantics types for an IL. Requires spec citations. |
| **implement** | Write a pass, interpreter, or pretty-printer. |
| **test** | Write unit tests, e2e tests, add Test262 coverage. |
| **prove** | Work on a simulation proof. Follow automation-first. |
| **review** | Check recent commits for regressions, duplicated code, architectural drift. Update docs. |
| **dedup** | Find and coalesce reimplemented utility code (LLMs do this constantly). |
| **escalate** | Inspect a `PROOF_BLOCKERS.md` entry. Determine if the property is false or the implementation needs restructuring. Write recommendation. |
| **flagship** | Work on compiling a flagship target (Prettier/Babel/tsc). File bugs as failing tests. |

---

## Mitigations for Known Agent Failure Modes

These are drawn directly from Anthropic's experience building a C compiler with agent teams. Every one of these problems occurred in their project. Our prompt and harness must prevent them.

### 1. New features break existing functionality

**The problem**: Anthropic found that agents frequently broke existing functionality each time they implemented a new feature.

**Mitigation**: Strict regression gate. `./tests/run_tests.sh --fast` is a pre-push hook. If any previously-passing test fails, the push is rejected. The `--fast` path runs only lightweight regression checks (unit/e2e sampling/wasm validation) and intentionally skips flagship parser sweeps. Full suite runs in CI on every merge to `main`.

```bash
# pre-push hook (installed in every subagent workspace)
#!/bin/bash
./tests/run_tests.sh --fast || { echo "ERROR: regression detected. Fix before pushing."; exit 1; }
./scripts/sorry_report.sh || { echo "ERROR: sorry threshold exceeded."; exit 1; }
```

### 2. Context window pollution

**The problem**: "The test harness should not print thousands of useless bytes."

**Mitigation**: All test runners print **one summary line per suite** to stdout. Full output goes to `test_logs/`. Error lines start with `ERROR:` for grep. The sorry report, diagnostic aggregator, and test harness all follow this rule.

```bash
# Good: one-line summary
echo "Test262: 4521/4600 passed (98.3%) — 79 failures logged to test_logs/test262.log"

# Bad: printing every test case
```

Pre-compute aggregate statistics. Never make the agent count things manually.

### 3. Time blindness

**The problem**: Agents can be time-blind and may spend far too long running tests.

**Mitigation**: Keep `--fast` short and run heavyweight checks only in `--full`. For parser work, run fail-fast coverage first via project-by-project smoke gates (`prettier`, then `babel`, then `TypeScript`) using `./scripts/parse_flagship_failfast.sh --project <name> --sample-per-project 200`, then confirm with `./scripts/parse_flagship_failfast.sh --full`. Long-sequence integration sweeps remain `./scripts/parse_flagship.sh --full --integration-only`. The test harness prints wall-clock elapsed time and warns after 5 minutes:

```bash
if [ "$SECONDS" -gt 300 ]; then
  echo "WARNING: test run exceeding 5 minutes. Consider --fast."
fi
```

### 4. Multiple agents solving the same problem

**The problem**: "Every agent would hit the same bug, fix that bug, and then overwrite each other's changes."

**Mitigation**: Lock files in `current_tasks/` with git-based synchronization (see Agent Startup Protocol above). Additionally, when agents work on the flagship target (one giant task), use **Node.js as an oracle** for bisection — analogous to how Anthropic used GCC as an oracle for the Linux kernel. Compile most of the target with a known-working approach (e.g., run in Node.js), swap in VerifiedJS-compiled subsets, and narrow down which function/module is broken.

### 5. Orientation cost

**The problem**: "Each agent is dropped into a fresh workspace with no context and will spend significant time orienting itself."

**Mitigation**: `ARCHITECTURE.md`, `PROGRESS.md`, `TASKS.md`, and `PROOF_BLOCKERS.md` are the agent's context. This README instructs every agent to read these first. These files are kept short and current — updating them is itself a task type.

### Anthropic Blog Reminder (Operational Guardrails)

- Use short feedback loops (`--fast` tests, narrow diffs, one task per run).
- Prevent context bloat (one-line summaries; logs to files).
- Prefer checkpointed progress (`TASKS.md`, `PROGRESS.md`, `PROOF_BLOCKERS.md`) over memory.
- Force isolation with `git worktree` so subagents do not trample each other.
- If a tactic fails repeatedly, log it and pivot; do not retry blindly.

### 6. Code duplication

**The problem**: "LLM-written code frequently re-implements existing functionality."

**Mitigation**: `dedup` is a first-class task type in `TASKS.md`. Agents performing review should grep for patterns like duplicate helper functions, reimplemented list operations, or redundant type conversions. When found, coalesce into a shared `Util.lean` module and update all call sites.

### 7. Agents spending time on already-failed approaches

**The problem**: Agents retry the same broken approach without learning from prior failures.

**Mitigation**: `PROOF_BLOCKERS.md` records failed proof attempts with the goal state and the approaches tried. Agents must read this file before starting proof work. When an agent fails, it appends to this file rather than just giving up silently. Format:

```markdown
### ClosureConvertCorrect.lean:87 — `closure_env_lookup`
**Goal**: `∀ x ∈ env, lookup (convert env) x = some (convert_val (env.get x))`
**Attempts**:
1. Induction on env — stuck on cons case, `simp` doesn't simplify
2. Tried `grind` — timeout after 60s
3. Tried restructuring as a well-founded recursion — type mismatch
**Status**: ESCALATE — may need to change `convert` to carry an auxiliary proof
```

---

## Testing Strategy

### Unit Tests (per-pass, in Lean)

```lean
-- Tests/Core/Elaborate.lean
-- SPEC: §13.3.1 Let and Const Declarations
#eval do
  let src := "let x = 1 + 2; console.log(x);"
  let ast ← JS.parse src
  let core ← JS.elaborate ast
  let result ← JS.Core.interp core
  assert! result.stdout == ["3"]
```

### End-to-End Tests

1. **Test262**: compile each test, run on `wasmtime`, compare against `node`. Track pass rate.
2. **Flagship targets**: Prettier → Babel → Three.js → tsc.
3. **Differential fuzzing**: random JS via jsfunfuzz, compile, compare against Node.js.

### Test Harness Design (for agents, not humans)

```bash
#!/bin/bash
# tests/run_tests.sh
# --fast: lightweight regression checks only
# --full: includes heavyweight suites
# Output: one summary line to stdout. Details to test_logs/.

MODE="${1:---fast}"
SEED=$(echo "$HOSTNAME" | md5sum | head -c 8)
LOGDIR="test_logs/$(date +%Y%m%d_%H%M%S)"
mkdir -p "$LOGDIR"

# Lean unit tests
lake test > "$LOGDIR/unit.log" 2>&1
UNIT_PASS=$(grep -c "PASS" "$LOGDIR/unit.log" || true)
UNIT_FAIL=$(grep -c "FAIL" "$LOGDIR/unit.log" || true)

# E2E tests (sample or full)
if [ "$MODE" = "--fast" ]; then
  ./scripts/run_e2e.sh --seed "$SEED" --sample 0.05 > "$LOGDIR/e2e.log" 2>&1
else
  ./scripts/run_e2e.sh > "$LOGDIR/e2e.log" 2>&1
fi
E2E_PASS=$(grep -c "^PASS" "$LOGDIR/e2e.log" || true)
E2E_FAIL=$(grep -c "^FAIL" "$LOGDIR/e2e.log" || true)

# Flagship parser sweep (full mode only; integration tests only)
if [ "$MODE" != "--fast" ]; then
  ./scripts/parse_flagship.sh --full --integration-only > "$LOGDIR/parse_flagship.log" 2>&1 || true
fi

# Wasm validation
./scripts/validate_wasm.sh > "$LOGDIR/validate.log" 2>&1
VALID=$(grep -c "^VALID" "$LOGDIR/validate.log" || true)
INVALID=$(grep -c "^INVALID" "$LOGDIR/validate.log" || true)

# One-line summary
echo "Tests: unit=$UNIT_PASS/$((UNIT_PASS+UNIT_FAIL)) e2e=$E2E_PASS/$((E2E_PASS+E2E_FAIL)) wasm=$VALID/$((VALID+INVALID)) — logs in $LOGDIR"

# Exit nonzero if any regression
[ "$UNIT_FAIL" -eq 0 ] && [ "$E2E_FAIL" -eq 0 ] && [ "$INVALID" -eq 0 ]
```

### Validation Tools

- `wasm-tools validate` on every `.wasm` output
- Valex-style binary checker: compare serialized `.wasm` against `Wasm.AST`

---

## Project Structure

```
verifiedjs/
├── README.md                ← this file
├── TASKS.md                 ← master task list (greedy pull)
├── PROGRESS.md              ← per-pass status
├── FAILURES.md              ← failing tests with minimal repros
├── ARCHITECTURE.md          ← IL descriptions, TCB boundary, spec ambiguities
├── PROOF_BLOCKERS.md        ← stuck goals with failed approaches
├── SORRY_REPORT.md          ← auto-generated
├── .mcp.json                ← lean-lsp-mcp config
├── current_tasks/           ← agent lock files
├── agent_logs/
├── lakefile.lean
├── lean-toolchain
│
├── VerifiedJS/
│   ├── Source/
│   │   ├── Lexer.lean
│   │   ├── Parser.lean
│   │   ├── AST.lean         ← SPEC: §11–15 (Expressions, Statements, etc.)
│   │   └── Print.lean
│   │
│   ├── Core/
│   │   ├── Syntax.lean      ← SPEC: desugared subset
│   │   ├── Semantics.lean   ← SPEC: §8 (Executable Code), §9 (Ordinary Objects)
│   │   ├── Interp.lean
│   │   ├── Print.lean
│   │   └── Elaborate.lean
│   │
│   ├── Flat/
│   │   ├── Syntax.lean
│   │   ├── Semantics.lean
│   │   ├── Interp.lean
│   │   ├── Print.lean
│   │   └── ClosureConvert.lean
│   │
│   ├── ANF/
│   │   ├── Syntax.lean
│   │   ├── Semantics.lean
│   │   ├── Interp.lean
│   │   ├── Print.lean
│   │   ├── Convert.lean
│   │   └── Optimize.lean     ← STUB: identity pass
│   │
│   ├── Wasm/
│   │   ├── Syntax.lean
│   │   ├── Typing.lean
│   │   ├── Semantics.lean
│   │   ├── Numerics.lean
│   │   ├── Interp.lean
│   │   ├── Print.lean        ← WAT printer
│   │   ├── IR.lean
│   │   ├── IRInterp.lean
│   │   ├── IRPrint.lean
│   │   ├── Lower.lean
│   │   ├── Emit.lean
│   │   └── Binary.lean
│   │
│   ├── Runtime/
│   │   ├── GC.lean
│   │   ├── Values.lean
│   │   ├── Objects.lean
│   │   ├── Strings.lean
│   │   ├── Regex.lean
│   │   └── Generators.lean
│   │
│   ├── Proofs/
│   │   ├── ElaborateCorrect.lean
│   │   ├── ClosureConvertCorrect.lean
│   │   ├── ANFConvertCorrect.lean
│   │   ├── OptimizeCorrect.lean
│   │   ├── LowerCorrect.lean
│   │   ├── EmitCorrect.lean
│   │   └── EndToEnd.lean     ← no sorrys allowed after Phase 2
│   │
│   ├── Util.lean             ← shared helpers (dedup target)
│   └── Driver.lean
│
├── tests/
│   ├── unit/
│   ├── e2e/
│   ├── test262/              ← git submodule
│   ├── flagship/             ← git submodules: prettier, babel, TypeScript
│   └── run_tests.sh
│
└── scripts/
    ├── sorry_report.sh
    ├── run_e2e.sh
    ├── lake_build_concise.sh
    ├── run_flagship_cycles.sh
    ├── bisect.sh             ← oracle-based IL-level bisection
    ├── validate_wasm.sh
    └── lsp_diagnostics.py
```

---

## Full ECMAScript 2020

The compiler targets **all** of ECMAScript 2020 (SPEC: https://tc39.es/ecma262/2020/). No feature is excluded. Features are implemented incrementally but none are out of scope.

This means: `class` (SPEC §14.6), `async/await` (SPEC §14.7–14.8), generators (SPEC §14.4), `for-in`/`for-of` (SPEC §13.7), destructuring (SPEC §13.15.5), spread/rest, `Proxy`/`Reflect` (SPEC §26, §28), `Symbol` (SPEC §19.4), `WeakMap`/`WeakSet` (SPEC §23.3–23.4), `Promise` (SPEC §25.6), full prototype chains (SPEC §9.1), `eval` (SPEC §18.2.1), `with` (SPEC §13.11), `arguments` (SPEC §9.4.4), tagged template literals (SPEC §12.3.7), optional chaining, nullish coalescing, regex (SPEC §21.2), modules (SPEC §15), dynamic `import()`, `SharedArrayBuffer`/`Atomics` (SPEC §24.2, §24.4), iterators (SPEC §25.1), computed property names, label statements, and every other specified feature.

### Formalization Strategy

Formalize incrementally:
0. Implement parser/lexer end to end, make sure it runs on everything first.
1. Computational core: primitives, let/const, functions, closures, objects, arrays, control flow (SPEC §6–8, §12–13)
2. Classes, prototypes, `this` (SPEC §9, §14.6)
3. Generators, async/await (SPEC §14.4, §14.7–14.8, §25.6)
4. Proxy, Symbol, WeakMap (SPEC §19.4, §23.3, §26)
5. Modules, eval, regex (SPEC §15, §18.2.1, §21.2)

Each increment extends `Syntax.lean` and `Semantics.lean` monotonically. Design the semantics so existing proofs do not break when new features are added.

---

## Build & Run

```bash
./scripts/lake_build_concise.sh                 # concise build summary (warnings hidden by default)
lake build                                      # full build output
lake exe verifiedjs input.js -o output.wasm     # compile
lake exe verifiedjs input.js --parse-only       # parser-only check
wasmtime output.wasm                             # run
lake exe verifiedjs input.js --emit=core        # inspect IL
lake exe verifiedjs input.js --run=anf          # interpret at ANF
lake test                                        # Lean unit tests
./tests/run_tests.sh --fast                      # lightweight regression checks
./tests/run_tests.sh --full                      # full suites (includes flagship parse integration sweep)
./scripts/parse_flagship_failfast.sh --project prettier --sample-per-project 200   # parser smoke gate 1 (benchmark-first)
./scripts/parse_flagship_failfast.sh --project babel --sample-per-project 200      # parser smoke gate 2
./scripts/parse_flagship_failfast.sh --project TypeScript --sample-per-project 200  # parser smoke gate 3 (heaviest last)
./scripts/parse_flagship_failfast.sh --full                # parser completion gate (all flagship JS files)
./scripts/parse_flagship.sh --full --integration-only  # long-sequence parser gate
./scripts/sorry_report.sh                        # sorry report
git submodule update --init --recursive          # fetch all submodules (test262 + flagship repos)
./scripts/run_flagship_cycles.sh --dry-run       # show flagship build cycle + Lean compile plan
./scripts/run_flagship_cycles.sh                 # run build cycles + compile entrypoints with verifiedjs
./scripts/run_e2e.sh tests/flagship/prettier/    # flagship target
./scripts/agent_supervisor.sh spawn --count 3 --dry-run       # create N agent worktrees and run one round
./scripts/agent_supervisor.sh supervise --count 2 --max-rounds 10  # keep spawning rounds until tests pass
```

`scripts/agent_supervisor.sh` assigns tasks centrally from `TASKS.md` and uses atomic local locks in `.agent_locks/` to prevent duplicate task claims across parallel worktrees.
At the end of each run it prints a supervisor summary (rounds, agent exits, test status, completed/failed task list, log paths).

---

## Key Principles for Agents

1. **Read `TASKS.md` first.** Pick the highest-priority unclaimed task. Lock it. Do it. Push. Exit.
2. **Cite the spec.** Every semantic rule in Lean must reference the ECMA-262 §section it implements.
3. **Every IL must be inspectable.** Syntax + Semantics + Interpreter + Printer. No exceptions.
4. **Automation first in proofs.** Try `decide`/`simp`/`omega`/`grind`/`canonical`/`aesop` before manual proof.
5. **Use the LSP.** Query diagnostics, goal states, hover, LeanSearch/Loogle.
6. **Every change must pass `./tests/run_tests.sh --fast`.** No regressions.
7. **Parser/lexer/AST changes must run parser fail-fast gates**: run project-by-project smoke gates (`prettier`, `babel`, `TypeScript`) with `--sample-per-project 200`; use `--full` before claiming parser completion.
8. **No context pollution.** Print one-line summaries. Log details to files.
9. **Update coordination files** (`TASKS.md`, `PROGRESS.md`) before pushing.
   If you discover new required work, add it as a new unchecked task in `TASKS.md` (with priority/dependency note).
10. **Small commits.** One logical change per commit. Easier to merge, easier to bisect.
11. **When stuck on a proof >30 minutes**, file in `PROOF_BLOCKERS.md` with the goal state and failed approaches. Move on.
12. **If a proof has failed 3+ times**, mark `ESCALATE:` in `PROOF_BLOCKERS.md`. The property might be false.
13. **When an e2e test fails**, bisect using `--run=<IL>` interpreters.
14. **Do not proliferate sorrys.** Check `SORRY_REPORT.md`. If near threshold, close existing sorrys first.
15. **Design for provability.** If an implementation is correct but hard to prove, refactor it.
16. **Watch for code duplication.** If you see reimplemented helpers, coalesce into `Util.lean`.
17. **Interfaces first.** Define types and theorem signatures before implementations.
18. **Read `PROOF_BLOCKERS.md` before starting proof work.** Do not retry approaches that already failed.
