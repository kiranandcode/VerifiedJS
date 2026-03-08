# VerifiedJS — Progress Tracker

## Pipeline Status

| Pass | Syntax | Semantics | Interp | Print | Pass Impl | Proof |
|------|--------|-----------|--------|-------|-----------|-------|
| Source (AST) | ✅ full ES2020 | N/A | N/A | baseline | N/A | N/A |
| Lexer/Parser | ✅ | N/A | N/A | N/A | ✅ recursive descent (96.30% flagship coverage, 1976/2052 on 2026-03-08) | N/A |
| Core | ✅ | ✅ `step?` | ✅ small-step driver | ✅ full pretty-printer | Elaborate: ✅ (stubs for classes/for-in/destructuring) | stub |
| Flat | ✅ | ✅ `step?` (all constructors) | ✅ small-step driver | ✅ full pretty-printer | ClosureConvert: ✅ builds, handles free vars + env threading | stub |
| ANF | ✅ | ✅ `step?`, `Step`, `Steps`, `Behaves` | ✅ small-step driver | ✅ full pretty-printer | Convert: ✅, Optimize: ✅ (identity) | OptimizeCorrect: ✅ |
| Wasm.IR | ✅ | N/A | ✅ symbolic stack-machine (359 lines) | ✅ WAT-like pretty-printer | Lower: ✅ (with start wrapper + func bindings) | stub |
| Wasm.AST | ✅ | ✅ `step?`, `Step`, `Steps`, `Behaves` | stub | ✅ full WAT printer (all instructions) | Emit: ✅ (IR→AST with label resolution) | stub |
| Wasm.Binary | N/A | N/A | N/A | N/A | ✅ full encoder (LEB128 + all sections) | N/A |

## End-to-End Pipeline Status

**Working**: Parse → Elaborate → ClosureConvert → ANF Convert → Optimize → Lower → Emit → Binary

- Simple arithmetic programs compile to valid .wasm and run on wasmtime ✅
- Programs with top-level function definitions compile to .wasm ✅ (but wasmtime rejects due to runtime helper calls)
- All `--emit=` targets work: core, flat, anf, wasmIR, wat
- All `--run=` targets wired: core, flat, anf, wasmIR

### Known Wasm Runtime Issues

1. **Runtime helper functions missing**: Programs with function calls emit `call RuntimeIdx.*` (indices 0-15) but no runtime functions are defined in the module. Wasmtime rejects with "function index out of bounds".
2. **Value representation (partial)**: Lowering now carries JS values through `f64` with boxed placeholders and emits numeric ops via `f64` paths. Full NaN-box payload tagging/runtime decoding is still pending.
3. **Global lookup semantics (partial)**: unresolved identifiers lower through `__rt_getGlobal`; helper currently returns `undefined` placeholder.
4. **Start function already fixed**: Added zero-param `_start` wrapper (Wasm spec requires start functions take no params).

## Runtime Status

| Component | Status |
|-----------|--------|
| Values (NaN-boxing) | stub |
| GC (mark-sweep) | stub |
| Objects | stub |
| Strings | stub |
| Regex | stub |
| Generators/Async | stub |

## E2E Test Status

- 10 handcrafted test cases in `tests/e2e/`
- Pipeline stage tests: parse/elaborate/flat/anf/wasmIR/wat/compile
- Metamorphic tests: Core vs Flat vs ANF interpreter trace comparison
- Wasm validation: wasmtime execution for simple programs
- Node.js comparison: all test files valid JS

## Metrics

- Sorry count: TBD (run `./scripts/sorry_report.sh`)
- Test262 pass rate: deterministic full sample reached 274/500 passes, 0 fails, 23 xfails, 203 skips (`./scripts/run_test262_compare.sh --full --sample 500 --seed local`, 2026-03-08)
- Flagship parse rate: 96.30% (1976/2052)
- E2E tests: 10 handcrafted JS programs
