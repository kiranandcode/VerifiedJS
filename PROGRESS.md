# VerifiedJS — Progress Tracker

## Pipeline Status

| Pass | Syntax | Semantics | Interp | Print | Pass Impl | Proof |
|------|--------|-----------|--------|-------|-----------|-------|
| Source (AST) | partial | N/A | N/A | baseline | N/A | N/A |
| Lexer/Parser | partial | N/A | N/A | N/A | baseline (single-token expr + tokenization) | N/A |
| Core | defined | defined | stub | stub | Elaborate: stub | stub |
| Flat | defined | defined (`step?` explicit coverage for all `Flat.Expr` constructors) | stub | stub | ClosureConvert: stub | stub |
| ANF | partial | defined (`step?`, `Step`, `Steps`, `initialState`, `Behaves`) | stub | stub | Convert: implemented (full Flat.Expr coverage), Optimize: done (identity) | OptimizeCorrect: done |
| Wasm.IR | stub | N/A | stub | stub | Lower: implemented (ANF.Expr/ComplexExpr coverage with runtime helper call lowering) | stub |
| Wasm.AST | defined | defined (`step?`, `Step`, `Steps`, `initialStore`, `initialState`, `Behaves`; core control/stack/local/global/numeric subset + branch/call_indirect/memory.size/memory.grow/bulk-op stubs wired, no `not yet implemented` fallbacks) | stub | stub | Emit: stub, Binary: stub | stub |

## Runtime Status

| Component | Status |
|-----------|--------|
| Values (NaN-boxing) | stub |
| GC (mark-sweep) | stub |
| Objects | stub |
| Strings | stub |
| Regex | stub |
| Generators/Async | stub |

## Metrics

- Sorry count: TBD (run `./scripts/sorry_report.sh`)
- Test262 pass rate: N/A
- Unit tests: N/A
- 2026-03-08: `Define ANF.Semantics small-step LTS` completed in `VerifiedJS/ANF/Semantics.lean` (pending supervisor validation move in `TASKS.md`)
- 2026-03-08: `Define Wasm.Semantics (port from WasmCert-Coq)` completed in `VerifiedJS/Wasm/Semantics.lean` (implemented `br*`, `call_indirect`, `memory.size`, `memory.grow`, and bulk-op executable stubs; pending supervisor validation move in `TASKS.md`)
