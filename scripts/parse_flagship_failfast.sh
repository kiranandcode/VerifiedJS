#!/bin/bash
# Fail-fast parser gate for flagship JavaScript codebases.
#
# Runs VerifiedJS parser (`--parse-only`) across flagship projects and exits on
# the first parse failure. Files under benchmark/benchmarks are processed first
# by default so parser regressions surface quickly on representative corpora.
#
# Usage:
#   ./scripts/parse_flagship_failfast.sh
#   ./scripts/parse_flagship_failfast.sh --project prettier --sample-per-project 200
#   ./scripts/parse_flagship_failfast.sh --project prettier
#   ./scripts/parse_flagship_failfast.sh --full --no-benchmarks-first
#   ./scripts/parse_flagship_failfast.sh --benchmarks-only

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
FLAGSHIP_DIR="${ROOT_DIR}/tests/flagship"
MAX_FILES="0"
SAMPLE_PER_PROJECT="0"
BENCHMARKS_FIRST="1"
BENCHMARKS_ONLY="0"
projects=(prettier babel TypeScript)

usage() {
  cat <<'EOF'
Usage: ./scripts/parse_flagship_failfast.sh [options]

Options:
  --full                   Parse all candidate files (default behavior)
  --sample-per-project N   Parse only first N ordered files per project (0 = all)
  --project NAME           Restrict to one project (repeatable)
  --max-files N            Stop after N selected files (0 = unlimited)
  --benchmarks-only        Parse only benchmark/benchmarks files
  --no-benchmarks-first    Disable benchmark-first ordering
  -h, --help               Show this help
EOF
}

require_cmd() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "ERROR: required command not found: $1" >&2
    exit 1
  fi
}

parse_file_or_fail() {
  local file="$1"
  if "$BIN_PATH" "$file" --parse-only >/dev/null 2>&1; then
    echo "PARSE_PASS $file"
    return 0
  fi
  echo "PARSE_FAIL $file"
  return 1
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --full)
      SAMPLE_PER_PROJECT="0"
      shift
      ;;
    --sample-per-project)
      SAMPLE_PER_PROJECT="${2:?missing value for --sample-per-project}"
      shift 2
      ;;
    --project)
      if [ "${projects[*]}" = "prettier babel TypeScript" ]; then
        projects=()
      fi
      projects+=("${2:?missing value for --project}")
      shift 2
      ;;
    --max-files)
      MAX_FILES="${2:?missing value for --max-files}"
      shift 2
      ;;
    --benchmarks-only)
      BENCHMARKS_ONLY="1"
      shift
      ;;
    --no-benchmarks-first)
      BENCHMARKS_FIRST="0"
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "Unknown arg: $1" >&2
      usage >&2
      exit 1
      ;;
  esac
done

require_cmd git
require_cmd awk
require_cmd find

if [ ! -d "$FLAGSHIP_DIR" ]; then
  echo "ERROR: flagship directory missing: $FLAGSHIP_DIR" >&2
  exit 1
fi

BIN_PATH="${ROOT_DIR}/.lake/build/bin/verifiedjs"
if [ ! -x "$BIN_PATH" ]; then
  lake build verifiedjs >/dev/null
fi
if [ ! -x "$BIN_PATH" ]; then
  echo "ERROR: missing verifiedjs binary at $BIN_PATH" >&2
  exit 1
fi

COMMON_GIT_DIR="$(git -C "$ROOT_DIR" rev-parse --git-common-dir)"
SHARED_WORKTREE_ROOT="$(cd "${COMMON_GIT_DIR}/.." && pwd)"
SHARED_FLAGSHIP_DIR="${SHARED_WORKTREE_ROOT}/tests/flagship"

TOTAL_SELECTED=0
TOTAL_PASS=0
START_TS="$(date +%s)"

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

for project in "${projects[@]}"; do
  project_dir="${FLAGSHIP_DIR}/${project}"
  if [ ! -d "$project_dir" ]; then
    shared_project_dir="${SHARED_FLAGSHIP_DIR}/${project}"
    if [ -d "$shared_project_dir" ]; then
      project_dir="$shared_project_dir"
    else
      echo "ERROR: project missing: $project_dir" >&2
      exit 1
    fi
  fi

  bench_list="${tmpdir}/${project}_bench.list"
  rest_list="${tmpdir}/${project}_rest.list"
  ordered_list="${tmpdir}/${project}_ordered.list"
  : > "$bench_list"
  : > "$rest_list"
  : > "$ordered_list"

  find "$project_dir" \
    -type d \( -name .git -o -name node_modules -o -name dist -o -name build -o -name built -o -name coverage -o -name .yarn \) -prune -o \
    -type f \( -name "*.js" -o -name "*.mjs" -o -name "*.cjs" \) \( -path "*/benchmark/*" -o -path "*/benchmarks/*" \) -print | LC_ALL=C sort > "$bench_list"

  if [ "$BENCHMARKS_ONLY" != "1" ]; then
    find "$project_dir" \
      -type d \( -name .git -o -name node_modules -o -name dist -o -name build -o -name built -o -name coverage -o -name .yarn \) -prune -o \
      -type f \( -name "*.js" -o -name "*.mjs" -o -name "*.cjs" \) ! -path "*/benchmark/*" ! -path "*/benchmarks/*" -print | LC_ALL=C sort > "$rest_list"
  fi

  if [ "$BENCHMARKS_FIRST" = "1" ]; then
    cat "$bench_list" "$rest_list" | awk '!seen[$0]++' > "$ordered_list"
  else
    cat "$rest_list" "$bench_list" | awk '!seen[$0]++' > "$ordered_list"
  fi

  PROJECT_SELECTED=0
  PROJECT_PASS=0
  while IFS= read -r file; do
    if [ -z "$file" ]; then
      continue
    fi
    if [ "$MAX_FILES" -gt 0 ] && [ "$TOTAL_SELECTED" -ge "$MAX_FILES" ]; then
      break 2
    fi
    if [ "$SAMPLE_PER_PROJECT" -gt 0 ] && [ "$PROJECT_SELECTED" -ge "$SAMPLE_PER_PROJECT" ]; then
      break
    fi
    PROJECT_SELECTED=$((PROJECT_SELECTED + 1))
    TOTAL_SELECTED=$((TOTAL_SELECTED + 1))
    if parse_file_or_fail "$file"; then
      PROJECT_PASS=$((PROJECT_PASS + 1))
      TOTAL_PASS=$((TOTAL_PASS + 1))
    else
      elapsed="$(( $(date +%s) - START_TS ))"
      echo "ParseFailFast[$project]: pass=$PROJECT_PASS selected=$PROJECT_SELECTED"
      echo "ParseFailFast: FAIL after selected=$TOTAL_SELECTED pass=$TOTAL_PASS elapsed=${elapsed}s samplePerProject=$SAMPLE_PER_PROJECT benchmarksFirst=$BENCHMARKS_FIRST"
      exit 1
    fi
  done < "$ordered_list"

  echo "ParseFailFast[$project]: pass=$PROJECT_PASS selected=$PROJECT_SELECTED"
done

elapsed="$(( $(date +%s) - START_TS ))"
echo "ParseFailFast: PASS selected=$TOTAL_SELECTED pass=$TOTAL_PASS elapsed=${elapsed}s samplePerProject=$SAMPLE_PER_PROJECT benchmarksFirst=$BENCHMARKS_FIRST benchmarksOnly=$BENCHMARKS_ONLY"
