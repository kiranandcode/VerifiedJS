# Agent Memory (Lean + Workflow)

Purpose: capture recurring mistakes and fixes so future agents avoid repeating them.

## How to Add Entries

- Add only high-signal observations that were actually encountered.
- Keep each entry short and actionable.
- Prefer concrete failure -> fix format.
- Include date and context file/module.

Template:

```md
- [YYYY-MM-DD] Context: <file/module or task>
  Symptom: <error or failure mode>
  Fix: <what worked>
  Guardrail: <quick rule to prevent repeat>
```

## Pruning Rules

- Remove or rewrite tips that are vague, duplicated, or no longer useful.
- Keep only tips that have been useful at least twice or are high-impact.
- During cleanup, prefer fewer strong rules over many weak rules.

- [2026-03-08] Context: `VerifiedJS/Core/Semantics.lean`
  Symptom: Lean failed on recursive `Env` definitions with termination goals (`sizeOf p < sizeOf env`) and stdlib mismatches (`Array.get?`, `String.toFloat?`, `Int.ofFloat` not available as used).
  Fix: Flattened `Env` to non-recursive bindings and constrained semantics helpers to APIs known in this codebase.
  Guardrail: Prefer minimal, compile-checked primitives first; only introduce recursive records or numeric/string conversions after confirming exact Lean API names in this toolchain.
