# VerifiedJS — Progress Tracker

## Pipeline Status

| Pass | Syntax | Semantics | Interp | Print | Pass Impl | Proof |
|------|--------|-----------|--------|-------|-----------|-------|
| Source (AST) | partial | N/A | N/A | baseline | N/A | N/A |
| Lexer/Parser | partial | N/A | N/A | N/A | baseline (single-token expr + tokenization) | N/A |
| Core | defined | stub | stub | stub | Elaborate: stub | stub |
| Flat | stub | stub | stub | stub | ClosureConvert: stub | stub |
| ANF | stub | stub | stub | stub | Convert: stub, Optimize: done (identity) | OptimizeCorrect: done |
| Wasm.IR | stub | N/A | stub | stub | Lower: stub | stub |
| Wasm.AST | stub | stub | stub | stub | Emit: stub, Binary: stub | stub |

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
