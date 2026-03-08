#!/bin/bash
# Parse flagship JS sources with VerifiedJS parser and report coverage/failures.
#
# Usage:
#   ./scripts/parse_flagship.sh
#   ./scripts/parse_flagship.sh --full
#   ./scripts/parse_flagship.sh --sample 0.02 --seed my-seed
#   ./scripts/parse_flagship.sh --project prettier
#   ./scripts/parse_flagship.sh --full --integration-only

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
FLAGSHIP_DIR="${ROOT_DIR}/tests/flagship"
SAMPLE_RATE="0.02"
SEED="${HOSTNAME:-local}"
FULL="0"
PROJECT_FILTER=""
MAX_PER_PROJECT="0"
SCAN_CAP="0"
INTEGRATION_ONLY="0"
MIN_PASS_RATE="0.95"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --full) FULL="1"; shift ;;
    --sample) SAMPLE_RATE="$2"; shift 2 ;;
    --seed) SEED="$2"; shift 2 ;;
    --project) PROJECT_FILTER="$2"; shift 2 ;;
    --max-per-project) MAX_PER_PROJECT="$2"; shift 2 ;;
    --scan-cap) SCAN_CAP="$2"; shift 2 ;;
    --integration-only) INTEGRATION_ONLY="1"; shift ;;
    --min-pass-rate) MIN_PASS_RATE="$2"; shift 2 ;;
    *)
      echo "Unknown arg: $1" >&2
      exit 1
      ;;
  esac
done

if [ "$FULL" = "1" ]; then
  SAMPLE_RATE="1.0"
fi

if [ ! -d "$FLAGSHIP_DIR" ]; then
  echo "ERROR: flagship directory missing: $FLAGSHIP_DIR"
  exit 1
fi

COMMON_GIT_DIR="$(git -C "$ROOT_DIR" rev-parse --git-common-dir 2>/dev/null || true)"
ALT_ROOT=""
if [ -n "$COMMON_GIT_DIR" ]; then
  ALT_ROOT="$(cd "${COMMON_GIT_DIR}/.." && pwd)"
fi

VERIFIEDJS_BIN="${ROOT_DIR}/.lake/build/bin/verifiedjs"
if [ ! -x "$VERIFIEDJS_BIN" ] && [ -n "$ALT_ROOT" ] && [ -x "$ALT_ROOT/.lake/build/bin/verifiedjs" ]; then
  VERIFIEDJS_BIN="$ALT_ROOT/.lake/build/bin/verifiedjs"
fi
if [ ! -x "$VERIFIEDJS_BIN" ]; then
  lake -d "$ROOT_DIR" build verifiedjs >/dev/null 2>&1 || lake -d "$ROOT_DIR" build >/dev/null 2>&1 || true
fi
if [ ! -x "$VERIFIEDJS_BIN" ] && [ -n "$ALT_ROOT" ] && [ -x "$ALT_ROOT/.lake/build/bin/verifiedjs" ]; then
  VERIFIEDJS_BIN="$ALT_ROOT/.lake/build/bin/verifiedjs"
fi
if [ ! -x "$VERIFIEDJS_BIN" ]; then
  echo "ERROR: verifiedjs executable missing after build: $VERIFIEDJS_BIN"
  exit 1
fi

projects=(prettier babel TypeScript)
if [ -n "$PROJECT_FILTER" ]; then
  projects=("$PROJECT_FILTER")
fi

SHARED_WORKTREE_ROOT="$(cd "${COMMON_GIT_DIR}" && cd .. && pwd)"
SHARED_FLAGSHIP_DIR="${SHARED_WORKTREE_ROOT}/tests/flagship"

TOTAL_SELECTED=0
TOTAL_PASS=0
TOTAL_FAIL=0
TOTAL_SKIP=0

pick_file() {
  local file="$1"
  if [ "$SAMPLE_RATE" = "1.0" ]; then
    return 0
  fi
  local hash hex mod threshold
  hash=$(printf "%s:%s" "$SEED" "$file" | shasum | cut -c1-8)
  hex=$((16#$hash))
  mod=$((hex % 10000))
  threshold=$(awk -v r="$SAMPLE_RATE" 'BEGIN { printf("%d", r * 10000) }')
  [ "$mod" -lt "$threshold" ]
}

for project in "${projects[@]}"; do
  project_dir="${FLAGSHIP_DIR}/${project}"
  if [ ! -d "$project_dir" ]; then
    shared_project_dir="${SHARED_FLAGSHIP_DIR}/${project}"
    if [ -d "$shared_project_dir" ]; then
      project_dir="$shared_project_dir"
    else
      echo "ERROR: project missing: $project_dir"
      exit 1
    fi
  elif ! find "$project_dir" -type f \( -name "*.js" -o -name "*.mjs" -o -name "*.cjs" \) -print -quit | grep -q .; then
    shared_project_dir="${SHARED_FLAGSHIP_DIR}/${project}"
    if [ -d "$shared_project_dir" ]; then
      project_dir="$shared_project_dir"
    fi
  fi
  project_roots=("$project_dir")
  if [ "$INTEGRATION_ONLY" = "1" ]; then
    if [ -d "$project_dir/tests/integration" ]; then
      project_roots=("$project_dir/tests/integration")
    elif [ -d "$project_dir/test" ]; then
      project_roots=("$project_dir/test")
    elif [ -d "$project_dir/tests" ]; then
      project_roots=("$project_dir/tests")
    fi
  fi

  project_base="$project_dir"
  if ! find "$project_base" -type f \( -name "*.js" -o -name "*.mjs" -o -name "*.cjs" \) -print -quit | grep -q .; then
    alt_project_dir="${ALT_ROOT}/tests/flagship/${project}"
    if [ -n "$ALT_ROOT" ] && [ -d "$alt_project_dir" ] && \
       find "$alt_project_dir" -type f \( -name "*.js" -o -name "*.mjs" -o -name "*.cjs" \) -print -quit | grep -q .; then
      project_base="$alt_project_dir"
    fi
  fi

  project_roots=("$project_base")
  if [ "$INTEGRATION_ONLY" = "1" ]; then
    if [ -d "$project_base/tests/integration" ]; then
      project_roots=("$project_base/tests/integration")
    elif [ -d "$project_base/test" ]; then
      project_roots=("$project_base/test")
    elif [ -d "$project_base/tests" ]; then
      project_roots=("$project_base/tests")
    fi
  fi

  PROJECT_SELECTED=0
  PROJECT_PASS=0
  PROJECT_FAIL=0
  PROJECT_SKIP=0
  PROJECT_SCANNED=0

  while IFS= read -r file; do
    PROJECT_SCANNED=$((PROJECT_SCANNED + 1))
    if [ "$SCAN_CAP" -gt 0 ] && [ "$PROJECT_SCANNED" -gt "$SCAN_CAP" ]; then
      break
    fi

    if [ "$MAX_PER_PROJECT" -gt 0 ] && [ "$PROJECT_SELECTED" -ge "$MAX_PER_PROJECT" ]; then
      break
    fi

    if ! pick_file "$file"; then
      PROJECT_SKIP=$((PROJECT_SKIP + 1))
      continue
    fi

    PROJECT_SELECTED=$((PROJECT_SELECTED + 1))
    if "$VERIFIEDJS_BIN" "$file" --parse-only >/dev/null 2>&1; then
      PROJECT_PASS=$((PROJECT_PASS + 1))
      echo "PARSE_PASS $file"
    else
      PROJECT_FAIL=$((PROJECT_FAIL + 1))
      echo "PARSE_FAIL $file"
    fi
  done < <(
    find "${project_roots[@]}" \
      -type d \( -name .git -o -name node_modules -o -name dist -o -name build -o -name built -o -name coverage -o -name .yarn -o -name test -o -name tests -o -name __tests__ -o -name fixture -o -name fixtures -o -name benchmark -o -name benchmarks -o -name baselines -o -name reference \) -prune -o \
      -type f \( -name "*.js" -o -name "*.mjs" -o -name "*.cjs" \) -print | LC_ALL=C sort
  )

  TOTAL_SELECTED=$((TOTAL_SELECTED + PROJECT_SELECTED))
  TOTAL_PASS=$((TOTAL_PASS + PROJECT_PASS))
  TOTAL_FAIL=$((TOTAL_FAIL + PROJECT_FAIL))
  TOTAL_SKIP=$((TOTAL_SKIP + PROJECT_SKIP))

  if [ "$PROJECT_SELECTED" -gt 0 ]; then
    PROJECT_RATE=$(awk -v p="$PROJECT_PASS" -v s="$PROJECT_SELECTED" 'BEGIN { printf("%.2f", (100.0 * p) / s) }')
  else
    PROJECT_RATE="0.00"
  fi
  echo "ParseFlagship[$project]: pass=$PROJECT_PASS fail=$PROJECT_FAIL selected=$PROJECT_SELECTED skipped=$PROJECT_SKIP rate=${PROJECT_RATE}%"
done

if [ "$TOTAL_SELECTED" -eq 0 ]; then
  PASS_RATE="0.0000"
else
  PASS_RATE=$(awk -v p="$TOTAL_PASS" -v s="$TOTAL_SELECTED" 'BEGIN { printf("%.4f", p / s) }')
fi

echo "ParseFlagship: pass=$TOTAL_PASS fail=$TOTAL_FAIL selected=$TOTAL_SELECTED skipped=$TOTAL_SKIP passRate=$PASS_RATE sample=$SAMPLE_RATE integrationOnly=$INTEGRATION_ONLY"

if awk -v rate="$PASS_RATE" -v min="$MIN_PASS_RATE" 'BEGIN { exit !(rate >= min) }'; then
  exit 0
else
  echo "ERROR: pass rate $PASS_RATE is below minimum $MIN_PASS_RATE"
  exit 1
fi
