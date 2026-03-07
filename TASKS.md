# VerifiedJS — Task List

## Priority 1 (blocking — foundations)
- [ ] Define JS.Source.AST inductive types (full ECMAScript 2020) — SPEC: §11–15
- [ ] Implement JS.Source.Lexer (context-sensitive `/` handling) — SPEC: §11
- [ ] Implement JS.Source.Parser (recursive descent) — SPEC: §11–15
- [ ] Parser milestone: parse ≥95% of JS files in `tests/flagship/{prettier,babel,TypeScript}` via `scripts/parse_flagship.sh --full`
- [ ] Parser milestone: support multi-token expression/statement parsing (currently baseline single-token parse only)
- [ ] Define JS.Core.Syntax inductive types
- [ ] Define JS.Core.Semantics small-step LTS
- [ ] Define JS.Flat.Syntax inductive types
- [ ] Define JS.ANF.Syntax inductive types
- [ ] Define Wasm.Syntax (port from WasmCert-Coq)

## Priority 2 (important — passes and interpreters)
- [ ] Implement Core.Elaborate (JS.AST → JS.Core) — SPEC: §14.6, §13.15.5, §13.7
- [ ] Implement Flat.ClosureConvert (JS.Core → JS.Flat)
- [ ] Implement ANF.Convert (JS.Flat → JS.ANF)
- [ ] Implement Wasm.Lower (JS.ANF → Wasm.IR)
- [ ] Implement Wasm.Emit (Wasm.IR → Wasm.AST)
- [ ] Implement Wasm.Binary (Wasm.AST → .wasm)
- [ ] Write Core.Interp reference interpreter
- [ ] Write Flat.Interp reference interpreter
- [ ] Write ANF.Interp reference interpreter
- [ ] Write Wasm.IR.Interp reference interpreter
- [ ] Write Core.Print pretty-printer
- [ ] Write Flat.Print pretty-printer
- [ ] Write ANF.Print pretty-printer
- [ ] Write Wasm.Print WAT printer
- [ ] Write Wasm.IR.Print pretty-printer

## Priority 3 (proof work)
- [ ] Define Flat.Semantics small-step LTS
- [ ] Define ANF.Semantics small-step LTS
- [ ] Define Wasm.Semantics (port from WasmCert-Coq)
- [ ] Prove ElaborateCorrect.lean
- [ ] Prove ClosureConvertCorrect.lean
- [ ] Prove ANFConvertCorrect.lean
- [ ] Prove LowerCorrect.lean
- [ ] Prove EmitCorrect.lean
- [ ] Compose EndToEnd.lean

## Priority 4 (runtime)
- [ ] Implement Runtime.Values (NaN-boxing)
- [ ] Implement Runtime.GC (mark-sweep in Wasm)
- [ ] Implement Runtime.Objects (property maps in linear memory)
- [ ] Implement Runtime.Strings (interned UTF-16)
- [ ] Implement Runtime.Regex (DFA/NFA engine)
- [ ] Implement Runtime.Generators (CPS/state machines)

## Priority 5 (testing and validation)
- [ ] Set up Test262 test harness
- [ ] Write unit tests for each IL
- [ ] Write e2e tests (compile + run on wasmtime)
- [ ] Set up differential testing against Node.js
- [ ] Add nightly full parse sweep: `scripts/parse_flagship.sh --full` and persist failures to `FAILURES.md`
- [ ] Long-sequence parser gate: run `scripts/parse_flagship.sh --full --integration-only` before merging parser-heavy changes
- [ ] Keep `tests/run_tests.sh --fast` free of flagship parse scans; run flagship parse only in long-sequence/full test cycles
- [ ] Flagship: compile Prettier
- [ ] Flagship: compile Babel
- [ ] Flagship: compile tsc

## Priority 6 (quality)
- [ ] Write ARCHITECTURE.md with IL descriptions and TCB boundary
- [ ] Deduplicate utility code across modules
- [ ] Review and update spec citations
