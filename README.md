# VerifiedJS: A Formally Verified JavaScript-to-WebAssembly Compiler in Lean 4

## Mission

Build a formally verified compiler from **full JavaScript** (ECMAScript 2020) to WebAssembly, written entirely in Lean 4. The compiler's correctness—semantic preservation from source to target—is proved mechanically in Lean's type theory. The compiled output runs on any standard Wasm runtime. End-to-end behavior is validated against Node.js using Test262.

### Normative Reference

The **ECMAScript 2020 Language Specification** is the normative reference for all semantic decisions:

> **https://tc39.es/ecma262/2020/**

Every agent implementing or formalizing JS semantics must cite the specific section of this spec justifying the behavior. Lean docstrings on semantic rules should include the spec section number:

```lean
/-- ECMA-262 §13.15.2 Runtime Semantics: Evaluation — AssignmentExpression -/
inductive AssignmentEval : ... → Prop where
```

When the spec is ambiguous, document the ambiguity in `ARCHITECTURE.md` and pick the behavior that matches Node.js (v20 LTS).

### The Flagship Target

The compiler's "Linux kernel moment" is **compiling the TypeScript compiler (`tsc`) to WebAssembly and using it to typecheck real TypeScript projects**. `tsc` is ~130,000 lines of JavaScript, exercises every corner of the language, and is the single most widely-used JS tool in the world.

Secondary targets (in rough order of difficulty):

1. **Prettier** (~50k LOC) — format JS/TS files, diff output against native Prettier
2. **Babel** (~70k LOC) — transpile modern JS, compare output against native Babel
3. **Three.js examples** — compile a Three.js demo, render in a browser via Wasm
4. **TypeScript compiler** (~130k LOC) — the flagship

The flagship repos are tracked as git submodules under `tests/flagship/`.

---

## Quick Start: Try the Compiler

```bash
# 1. Build the compiler
lake build

# 2. Write a simple JS program
echo 'var x = 1 + 2; var y = x * 3;' > hello.js

# 3. Inspect intermediate representations
lake exe verifiedjs hello.js --emit=core      # Core IL (desugared JS)
lake exe verifiedjs hello.js --emit=flat      # Flat IL (closure-converted)
lake exe verifiedjs hello.js --emit=anf       # ANF IL (A-normal form)
lake exe verifiedjs hello.js --emit=wasmIR    # Wasm IR (structured control flow)
lake exe verifiedjs hello.js --emit=wat       # WebAssembly Text Format

# 4. Compile to .wasm binary
lake exe verifiedjs hello.js -o hello.wasm

# 5. Run with wasmtime (simple arithmetic programs work)
wasmtime hello.wasm

# 6. Run the e2e test suite
bash tests/e2e/run_e2e.sh
```

### Current Limitations

- **Runtime semantics are still stubbed**: Runtime helper functions are now emitted as valid Wasm and execute under `wasmtime`, but many helpers (`__rt_call`, property/global/object ops) still return placeholders instead of full ECMA-262 behavior
- **Globals**: Unbound identifiers are lowered via a runtime global-lookup stub (`__rt_getGlobal`) that currently returns `undefined`; semantic global object behavior is not implemented yet
- **Float precision**: Numbers are currently lowered as i32 pointers; proper NaN-boxing/tagged pointers needed
- **Single-file only**: No module resolution or import/export linking yet
- **Language features**: Classes, for-in/of, destructuring, optional chaining are stubbed in elaboration

---

## Architecture (CompCert-Derived)

The compiler is a pipeline of formally verified passes. Each pass transforms between two intermediate languages and is equipped with a Lean proof of semantic preservation (a forward simulation). Composition yields end-to-end correctness.

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
lake exe verifiedjs input.js --run=flat     # interpret at JS.Flat level
lake exe verifiedjs input.js --run=anf      # interpret at JS.ANF level
lake exe verifiedjs input.js --run=wasmIR   # interpret at Wasm.IR level
```

When an end-to-end test fails, bisect by running interpreters at each level to isolate which pass introduced the bug.

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
- Flagship parser gates: `./scripts/parse_flagship_failfast.sh --full`

---

## Runtime / Memory Model

- **Value representation**: NaN-boxing in f64, or tagged pointers in i64
- **Heap**: bump allocator + mark-sweep GC compiled into the Wasm module
- **Strings**: interned, UTF-16, stored in linear memory
- **Objects**: property maps as linked hash tables in linear memory
- **Closures**: `(function_index, environment_pointer)` pairs
- **Prototypes**: chain traversal in linear memory
- **Generators/async**: CPS transform in JS.Flat, state machines in Wasm.IR

The runtime is linked into every output module. Its semantics are axiomatic—document the TCB boundary in `ARCHITECTURE.md`.

---

## Language Server Integration

The project uses the **Lean LSP** via the **lean-lsp-mcp** MCP server (`github.com/oOo0oOo/lean-lsp-mcp`). Agents use LSP feedback as a primary signal, not just `lake build` exit codes.

### Agent Workflow with LSP

1. **Before editing**: query `lean_diagnostic_messages` on the target file.
2. **After editing**: save, wait for re-elaboration, query diagnostics again. Fix new errors before committing.
3. **For proofs**: use `lean_goal` to inspect proof state at a specific line/column.
4. **For exploration**: use `lean_hover_info` for types, `lean_completions` for lemmas.
5. **For search**: use `lean_leansearch` (LeanSearch), `lean_loogle` (Loogle), `lean_local_search` (ripgrep).

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

Based on the ECMAScript specification, write a parser for javascript. Iterate on the parser and AST until we can parse ALL benchmarks, and pretty-print them to equivalent ASTs.

### Phase 1: Interface Consensus (mostly complete)

Define all IL `Syntax.lean` types, all pass function signatures, all correctness theorem statements (with `sorry` bodies), and all `Semantics.lean` relation signatures. These are the contracts that enable parallel work.

### Phase 2: Parallel Extension (current phase)

Agents work on **different modules** in parallel. The interfaces stay roughly consistent. Each module (Source, Core, Flat, ANF, Wasm) can have independent agents working on:
- Implementation (pass, interpreter, pretty-printer)
- Proofs (correctness theorems for the pass)
- Tests (unit tests, e2e tests)

Code and proofs are dependent but can alternate: one agent implements a pass, another works on the proof for a previously-implemented pass.

### Phase 3: Proof Convergence

Implementation and proofs co-evolve. When stuck:
1. Try automation first (see Proof Automation below)
2. Break the goal into lemmas, sorry each, try automation on each
3. If stuck >30 minutes on a single goal, file in `PROOF_BLOCKERS.md` with the goal state
4. If a property has been attempted 3+ times and failed, flag it in `PROOF_BLOCKERS.md` with `ESCALATE:` prefix.

---

## Sorry Management

`sorry` is a coordination mechanism. Unchecked proliferation defeats verification.

### Sorry Rules

1. Every sorry must have a `-- TODO:` comment explaining what remains.
2. Sorrys in `Proofs/` are expected during development. Sorrys in `Syntax.lean` or `Semantics.lean` are bugs.
3. Sorry count tracked in CI. Threshold: 100 → 50 → 20 → 0.
4. Sorrys must not appear in `EndToEnd.lean` after Phase 2.

Run `./scripts/sorry_report.sh` to generate the current sorry report.

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

---

## Agent Team Structure

### Module-Based Parallelism

Agents work on **different modules** simultaneously. The pipeline's modular structure (Source, Core, Flat, ANF, Wasm) provides natural boundaries for parallel work. Each module has well-defined interfaces (`Syntax.lean`) that remain stable.

**Parallelization strategy**:
- **Different modules**: Two agents can safely work on `Core/Elaborate.lean` and `Wasm/Lower.lean` simultaneously — no conflicts.
- **Code vs proof on same module**: One agent implements `Flat.ClosureConvert`, another proves `Proofs/ClosureConvertCorrect.lean`. The proof agent works against the current interface; if implementation changes, the proof adapts.
- **Parser is independent**: Parser work never conflicts with backend passes.

### Task Coordination

All work is driven by coordination files. Agents read these on startup and pick greedily.

**`TASKS.md`** — the master task list. Maintained by all agents. Priority-ordered.

**`PROGRESS.md`** — per-pass status. Updated after completing work.

**`PROOF_BLOCKERS.md`** — goals agents are stuck on. Check this before starting proof work to avoid duplicating failed attempts.

### Agent Startup Protocol

Every agent, on every spawn:

1. Read `TASKS.md`. Pick the highest-priority unchecked task.
2. Read `PROGRESS.md` to understand what's done and what's in flight.
3. If the task is proof work, read `PROOF_BLOCKERS.md` to avoid repeating failed attempts.
4. Do the task. Run `lake build` to verify. Run `bash tests/e2e/run_e2e.sh` for e2e checks.
5. Update `TASKS.md` (mark done) and `PROGRESS.md` (update status).
6. If the task revealed additional required work, add new unchecked items to `TASKS.md`.

### Task Types

| Type | Description |
|---|---|
| **implement** | Write a pass, interpreter, or pretty-printer. |
| **test** | Write unit tests, e2e tests, add Test262 coverage. |
| **prove** | Work on a simulation proof. Follow automation-first. |
| **parser** | Improve parser coverage. Run flagship gates to verify. |
| **review** | Check for regressions, duplicated code, architectural drift. |
| **flagship** | Work on compiling a flagship target (Prettier/Babel/tsc). |

---

## Mitigations for Known Agent Failure Modes

### 1. New features break existing functionality

**Mitigation**: Strict regression gate. `lake build` + `bash tests/e2e/run_e2e.sh` before pushing. If any previously-passing test fails, fix it first.

### 2. Context window pollution

**Mitigation**: All test runners print **one summary line per suite** to stdout. Full output goes to `test_logs/`. Pre-compute aggregate statistics. Never make the agent count things manually.

### 3. Multiple agents solving the same problem

**Mitigation**: Agents work on **different modules**. The pipeline's modular structure provides natural separation. Use `TASKS.md` to claim tasks before starting.

### 4. Orientation cost

**Mitigation**: `PROGRESS.md`, `TASKS.md`, and `PROOF_BLOCKERS.md` are the agent's context. Read these first. Keep them short and current.

### 5. Code duplication

**Mitigation**: Shared helpers go in `Util.lean`. When reviewing, grep for duplicate helper functions and coalesce.

### 6. Agents spending time on already-failed approaches

**Mitigation**: `PROOF_BLOCKERS.md` records failed proof attempts. Read it before starting proof work.

---

## Testing Strategy

### Unit Tests (per-pass, in Lean)

```lean
#eval do
  let src := "let x = 1 + 2; console.log(x);"
  let ast ← JS.parse src
  let core ← JS.elaborate ast
  let result ← JS.Core.interp core
  assert! result.stdout == ["3"]
```

### End-to-End Tests

Located in `tests/e2e/`. The test harness (`tests/e2e/run_e2e.sh`) runs:

1. **Pipeline stage tests**: parse → core → flat → anf → wasmIR → wat → .wasm for each test file
2. **Metamorphic tests**: Core vs Flat vs ANF interpreter traces must match (semantic preservation)
3. **Wasm validation**: compiled .wasm runs on wasmtime
4. **Node.js comparison**: test files are valid JS that runs identically in Node.js

### Test262 Compiler-Comparison Harness

Use `scripts/run_test262_compare.sh` to compare Node.js syntax acceptance against VerifiedJS compilation on the embedded Test262 suite:

```bash
# Fast deterministic sample
./scripts/run_test262_compare.sh --fast --sample 60 --seed local

# Larger sample (used by full pipeline test runs)
./scripts/run_test262_compare.sh --full --sample 500 --seed local
```

The runner emits machine-parseable lines:

- `TEST262_PASS`: Node `--check` accepts and VerifiedJS compiles
- `TEST262_FAIL`: unexpected VerifiedJS compile failure
- `TEST262_XFAIL`: compile failure classified as known limitation
- `TEST262_SKIP`: metadata-based or limitation-based skip

Current skip/xfail filters intentionally avoid unsupported Test262 categories and known frontend/runtime gaps (negative tests, harness includes/flags, module/raw/async harness requirements, fixture files, and tests that rely on unsupported globals or stubbed features).

The harness injects a small prelude that defines `Test262Error`, `assert`, `assert.sameValue`, and `assert.notSameValue` when missing, so plain Test262 assertion-style tests can run without external harness includes.

Known backend structural bugs that currently produce Wasm validation failures are classified as `TEST262_XFAIL known-backend:wasm-validation` (instead of hard `FAIL`) to keep regressions focused on newly introduced issues.

### Validation Tools

- `wasmtime` on every `.wasm` output
- `wasm-tools validate` for spec conformance
- Node.js as differential oracle

---

## Build & Run

```bash
lake build                                      # full build
lake exe verifiedjs input.js -o output.wasm     # compile
lake exe verifiedjs input.js --parse-only       # parser-only check
wasmtime output.wasm                             # run
lake exe verifiedjs input.js --emit=core        # inspect IL
lake exe verifiedjs input.js --run=anf          # interpret at ANF
lake test                                        # Lean unit tests
bash tests/run_tests.sh --fast --profile pipeline # unit+e2e+test262+wasm summary
bash tests/e2e/run_e2e.sh                        # e2e tests
./scripts/run_test262_compare.sh --fast --sample 60 --seed local
./scripts/sorry_report.sh                        # sorry report
./scripts/parse_flagship_failfast.sh --full      # parser completion gate
```

---

## Project Structure

```
verifiedjs/
├── README.md                ← this file
├── TASKS.md                 ← master task list
├── PROGRESS.md              ← per-pass status
├── PROOF_BLOCKERS.md        ← stuck goals with failed approaches
├── lakefile.lean
├── lean-toolchain
│
├── VerifiedJS/
│   ├── Source/
│   │   ├── Lexer.lean
│   │   ├── Parser.lean
│   │   ├── AST.lean         ← SPEC: §11–15
│   │   └── Print.lean
│   │
│   ├── Core/
│   │   ├── Syntax.lean      ← SPEC: desugared subset
│   │   ├── Semantics.lean   ← SPEC: §8, §9
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
│   │   └── Optimize.lean     ← identity pass (with proof)
│   │
│   ├── Wasm/
│   │   ├── Syntax.lean
│   │   ├── Semantics.lean
│   │   ├── IR.lean
│   │   ├── IRInterp.lean
│   │   ├── IRPrint.lean
│   │   ├── Lower.lean
│   │   ├── Emit.lean
│   │   ├── Print.lean        ← WAT printer
│   │   └── Binary.lean
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
│   ├── Util.lean             ← shared helpers
│   └── Driver.lean
│
├── tests/
│   ├── unit/
│   ├── e2e/                  ← handcrafted JS tests + run_e2e.sh
│   ├── test262/              ← git submodule
│   └── flagship/             ← git submodules: prettier, babel, TypeScript
│
└── scripts/
    ├── run_test262_compare.sh
    ├── sorry_report.sh
    ├── parse_flagship_failfast.sh
    └── validate_wasm.sh
```

---

## Full ECMAScript 2020

The compiler targets **all** of ECMAScript 2020 (SPEC: https://tc39.es/ecma262/2020/). No feature is excluded. Features are implemented incrementally but none are out of scope.

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

## Key Principles for Agents

1. **Read `TASKS.md` first.** Pick the highest-priority unclaimed task.
2. **Cite the spec.** Every semantic rule in Lean must reference the ECMA-262 §section it implements.
3. **Every IL must be inspectable.** Syntax + Semantics + Interpreter + Printer. No exceptions.
4. **Automation first in proofs.** Try `decide`/`simp`/`omega`/`grind`/`canonical`/`aesop` before manual proof.
5. **Use the LSP.** Query diagnostics, goal states, hover, LeanSearch/Loogle.
6. **Every change must build and pass e2e tests.** No regressions.
7. **No context pollution.** Print one-line summaries. Log details to files.
8. **Update coordination files** (`TASKS.md`, `PROGRESS.md`) after completing work.
9. **Small commits.** One logical change per commit.
10. **When stuck on a proof >30 minutes**, file in `PROOF_BLOCKERS.md` with the goal state and failed approaches.
11. **When an e2e test fails**, bisect using `--run=<IL>` interpreters.
12. **Design for provability.** If an implementation is correct but hard to prove, refactor it.
13. **Watch for code duplication.** Coalesce into `Util.lean`.
