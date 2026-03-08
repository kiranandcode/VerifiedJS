# VerifiedJS — Architecture

## Compilation Pipeline

```
JavaScript source
  │
  ├─ [1] Lexing + Parsing (outside TCB)
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
  ├─ [4] ANF conversion
  ▼
JS.ANF                    ← A-normal form
  │
  ├─ [5] Optimization passes (identity stub)
  ▼
JS.ANF                    ← unchanged
  │
  ├─ [6] Lowering to Wasm IR
  ▼
Wasm.IR                   ← structured control flow, Wasm types, linear memory ops
  │
  ├─ [7] Wasm IR → Wasm AST
  ▼
Wasm.AST                  ← abstract Wasm module
  │
  ├─ [8] Binary encoding (outside TCB)
  ▼
.wasm binary
```

## Wasm Backend Invariants

- `Wasm.IR.if_` carries an explicit result type (`Option IRType`).
- `Wasm.Emit` maps typed IR conditionals to Wasm block types (`if (result t)`), preventing invalid stack shapes at control-flow joins.
- Runtime helper functions in `Wasm.Lower` must annotate conditional result types consistently (`f64` for boxed JS values, `i32` for truthiness predicates).

These invariants are required for generated modules to validate under `wasmtime`/`wasm-tools`.

## Trusted Computing Base (TCB)

The following components are **outside** the TCB and validated by testing:
- Lexer + Parser (validated by Test262 + differential testing)
- Binary encoder (validated by wasm-tools + Valex-style checker)
- Runtime axioms (GC, string interning, etc.)

The following are **inside** the TCB (mechanically verified):
- All IL syntax definitions
- All IL semantics definitions
- All compilation passes (Elaborate, ClosureConvert, ANFConvert, Lower, Emit)
- All correctness proofs
- The proof composition in EndToEnd.lean

## Value Representation

NaN-boxing in f64. See `Runtime/Values.lean` for tag bit layout.

## Memory Model

- Linear memory with bump allocator + mark-sweep GC
- Strings: interned, UTF-16
- Objects: linked hash tables in linear memory
- Closures: (function_index, environment_pointer) pairs
- Prototypes: chain traversal

## Spec Ambiguities

(Document any ECMA-262 ambiguities and their resolution here)
