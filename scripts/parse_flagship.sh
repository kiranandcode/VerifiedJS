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

while [[ $# -gt 0 ]]; do
  case "$1" in
    --full) FULL="1"; shift ;;
    --sample) SAMPLE_RATE="$2"; shift 2 ;;
    --seed) SEED="$2"; shift 2 ;;
    --project) PROJECT_FILTER="$2"; shift 2 ;;
    --max-per-project) MAX_PER_PROJECT="$2"; shift 2 ;;
    --scan-cap) SCAN_CAP="$2"; shift 2 ;;
    --integration-only) INTEGRATION_ONLY="1"; shift ;;
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

projects=(prettier babel TypeScript)
if [ -n "$PROJECT_FILTER" ]; then
  projects=("$PROJECT_FILTER")
fi

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
    echo "ERROR: project missing: $project_dir"
    exit 1
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
    if lake exe verifiedjs "$file" --parse-only >/dev/null 2>&1; then
      PROJECT_PASS=$((PROJECT_PASS + 1))
      echo "PARSE_PASS $file"
    else
      PROJECT_FAIL=$((PROJECT_FAIL + 1))
      echo "PARSE_FAIL $file"
    fi
  done < <(
    find "${project_roots[@]}" \
      -type d \( -name .git -o -name node_modules -o -name dist -o -name build -o -name built -o -name coverage -o -name .yarn \) -prune -o \
      -type f \( -name "*.js" -o -name "*.mjs" -o -name "*.cjs" \) -print
  | LC_ALL=C sort)

  TOTAL_SELECTED=$((TOTAL_SELECTED + PROJECT_SELECTED))
  TOTAL_PASS=$((TOTAL_PASS + PROJECT_PASS))
  TOTAL_FAIL=$((TOTAL_FAIL + PROJECT_FAIL))
  TOTAL_SKIP=$((TOTAL_SKIP + PROJECT_SKIP))

  echo "ParseFlagship[$project]: pass=$PROJECT_PASS fail=$PROJECT_FAIL selected=$PROJECT_SELECTED skipped=$PROJECT_SKIP"
done

echo "ParseFlagship: pass=$TOTAL_PASS fail=$TOTAL_FAIL selected=$TOTAL_SELECTED skipped=$TOTAL_SKIP sample=$SAMPLE_RATE integrationOnly=$INTEGRATION_ONLY"

if [ "$TOTAL_FAIL" -gt 0 ]; then
  exit 1
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
