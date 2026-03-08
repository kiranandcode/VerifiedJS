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

- [2026-03-08] Context: `scripts/lsp_diagnostics.py`
  Symptom: Passing a Lean source file path as the output argument overwrote the source file with build logs.
  Fix: Restore the file from `git show HEAD:<path> > <path>` and avoid targeting tracked source paths for diagnostics output.
  Guardrail: Run diagnostics with default output behavior or an explicit log path under `test_logs/`/`/tmp`.

- [2026-03-08] Context: `VerifiedJS/Core/Semantics.lean`
  Symptom: Lean failed on recursive `Env` definitions with termination goals (`sizeOf p < sizeOf env`) and stdlib mismatches (`Array.get?`, `String.toFloat?`, `Int.ofFloat` not available as used).
  Fix: Flattened `Env` to non-recursive bindings and constrained semantics helpers to APIs known in this codebase.
  Guardrail: Prefer minimal, compile-checked primitives first; only introduce recursive records or numeric/string conversions after confirming exact Lean API names in this toolchain.

- [2026-03-08] Context: `tests/run_tests.sh --fast`
  Symptom: Harness failed before tests (`mktemp` under `test_logs/` and `find tests/e2e` missing directory).
  Fix: Create `test_logs/` and `tests/e2e/` in the worktree before running the suite.
  Guardrail: Run `mkdir -p test_logs tests/e2e` as a preflight for fresh worktrees.
