#!/bin/bash
# VerifiedJS test runner.
# --fast: 5% deterministic sample (seeded by $HOSTNAME)
# --full: everything
# Output: one summary line to stdout. Details to test_logs/.

set -euo pipefail

MODE="${1:---fast}"
SEED=$(echo "${HOSTNAME:-local}" | md5sum 2>/dev/null | head -c 8 || echo "deadbeef")
LOGDIR="test_logs/$(date +%Y%m%d_%H%M%S)"
mkdir -p "$LOGDIR"
SECONDS=0

# Lean unit tests
echo "Running Lean unit tests..." >&2
if lake test > "$LOGDIR/unit.log" 2>&1; then
  UNIT_STATUS="ok"
elif grep -q "no test driver configured" "$LOGDIR/unit.log"; then
  # Fallback: this repo currently uses a test library target instead of `lake test`.
  if lake build Tests >> "$LOGDIR/unit.log" 2>&1; then
    UNIT_STATUS="ok"
  else
    UNIT_STATUS="fail"
  fi
else
  UNIT_STATUS="fail"
fi
UNIT_PASS=$(grep -c "PASS\|✓\|passed" "$LOGDIR/unit.log" 2>/dev/null || true)
UNIT_FAIL=$(grep -c "FAIL\|✗\|failed" "$LOGDIR/unit.log" 2>/dev/null || true)

# E2E tests (sample or full)
E2E_PASS=0
E2E_FAIL=0
if [ -x "./scripts/run_e2e.sh" ]; then
  if [ "$MODE" = "--fast" ]; then
    ./scripts/run_e2e.sh --seed "$SEED" --sample 0.05 > "$LOGDIR/e2e.log" 2>&1 || true
  else
    ./scripts/run_e2e.sh > "$LOGDIR/e2e.log" 2>&1 || true
  fi
  E2E_PASS=$(grep -c "^PASS" "$LOGDIR/e2e.log" 2>/dev/null || true)
  E2E_FAIL=$(grep -c "^FAIL" "$LOGDIR/e2e.log" 2>/dev/null || true)
fi

# Flagship parse smoke tests (run only in --full; integration dirs only)
PARSE_PASS=0
PARSE_FAIL=0
if [ -x "./scripts/parse_flagship.sh" ]; then
  if [ "$MODE" != "--fast" ]; then
    ./scripts/parse_flagship.sh --full --integration-only > "$LOGDIR/parse_flagship.log" 2>&1 || true
    PARSE_PASS=$(grep -c "^PARSE_PASS " "$LOGDIR/parse_flagship.log" 2>/dev/null || true)
    PARSE_FAIL=$(grep -c "^PARSE_FAIL " "$LOGDIR/parse_flagship.log" 2>/dev/null || true)
  fi
fi

# Wasm validation
VALID=0
INVALID=0
if [ -x "./scripts/validate_wasm.sh" ]; then
  ./scripts/validate_wasm.sh > "$LOGDIR/validate.log" 2>&1 || true
  VALID=$(grep -c "^VALID" "$LOGDIR/validate.log" 2>/dev/null || true)
  INVALID=$(grep -c "^INVALID" "$LOGDIR/validate.log" 2>/dev/null || true)
fi

# Time warning
if [ "$SECONDS" -gt 300 ]; then
  echo "WARNING: test run exceeding 5 minutes ($SECONDS s). Consider --fast." >&2
fi

# One-line summary
echo "Tests: unit=$UNIT_PASS/$((UNIT_PASS+UNIT_FAIL))($UNIT_STATUS) e2e=$E2E_PASS/$((E2E_PASS+E2E_FAIL)) parse=$PARSE_PASS/$((PARSE_PASS+PARSE_FAIL)) wasm=$VALID/$((VALID+INVALID)) [${SECONDS}s] — logs in $LOGDIR"

# Exit nonzero if any regression
if [ "$UNIT_STATUS" = "fail" ] || [ "$E2E_FAIL" -gt 0 ] || [ "$INVALID" -gt 0 ]; then
  exit 1
fi
