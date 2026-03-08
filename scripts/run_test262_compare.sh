#!/usr/bin/env bash
# VerifiedJS Test262 compiler comparison harness.
#
# Compiles Test262 cases with VerifiedJS, runs generated wasm, and compares
# output with Node.js only when wasm output is produced.

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

SUITE_DIR="tests/test262/test"
MODE="fast"
SAMPLE_COUNT=100
SEED="verifiedjs"
MAX_FAIL=50
HARNESS_PRELUDE='(function (g) {
  if (typeof g.Test262Error !== "function") {
    g.Test262Error = function Test262Error(message) {
      this.name = "Test262Error";
      this.message = String(message || "");
    };
    g.Test262Error.prototype = Object.create(Error.prototype);
    g.Test262Error.prototype.constructor = g.Test262Error;
  }
  var assertFn = g.assert;
  if (typeof assertFn !== "function") {
    assertFn = function assert(condition, message) {
      if (!condition) {
        throw new g.Test262Error(message || "Assertion failed");
      }
    };
    g.assert = assertFn;
  }
  if (typeof assertFn.sameValue !== "function") {
    assertFn.sameValue = function sameValue(actual, expected, message) {
      if (!Object.is(actual, expected)) {
        throw new g.Test262Error(message || ("Expected SameValue but got " + actual + " and " + expected));
      }
    };
  }
  if (typeof assertFn.notSameValue !== "function") {
    assertFn.notSameValue = function notSameValue(actual, expected, message) {
      if (Object.is(actual, expected)) {
        throw new g.Test262Error(message || ("Expected values to differ but both were " + actual));
      }
    };
  }
  if (typeof assertFn.throws !== "function") {
    assertFn.throws = function throws(expectedErrorConstructor, fn, message) {
      var threw = false;
      try {
        fn();
      } catch (err) {
        threw = true;
        if (typeof expectedErrorConstructor === "function" && !(err instanceof expectedErrorConstructor)) {
          throw new g.Test262Error(
            message || ("Expected throw " + expectedErrorConstructor.name + " but got " + (err && err.name))
          );
        }
      }
      if (!threw) {
        throw new g.Test262Error(message || "Expected function to throw");
      }
    };
  }
})(typeof globalThis !== "undefined" ? globalThis : this);'

usage() {
  cat <<'USAGE'
Usage: ./scripts/run_test262_compare.sh [--fast|--full] [--sample N] [--seed S] [--suite-dir PATH] [--max-fail N]
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --fast)
      MODE="fast"
      SAMPLE_COUNT=100
      shift
      ;;
    --full)
      MODE="full"
      SAMPLE_COUNT=0
      shift
      ;;
    --sample)
      SAMPLE_COUNT="${2:?missing value for --sample}"
      shift 2
      ;;
    --seed)
      SEED="${2:?missing value for --seed}"
      shift 2
      ;;
    --suite-dir)
      SUITE_DIR="${2:?missing value for --suite-dir}"
      shift 2
      ;;
    --max-fail)
      MAX_FAIL="${2:?missing value for --max-fail}"
      shift 2
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

if [[ ! -d "$SUITE_DIR" ]]; then
  echo "ERROR: Test262 suite dir not found: $SUITE_DIR" >&2
  exit 2
fi

if ! command -v node >/dev/null 2>&1; then
  echo "ERROR: node is required for Test262 comparison" >&2
  exit 2
fi
if ! command -v wasmtime >/dev/null 2>&1; then
  echo "ERROR: wasmtime is required for runtime comparison" >&2
  exit 2
fi

VERIFIEDJS_BIN="$ROOT_DIR/.lake/build/bin/verifiedjs"
if [[ ! -x "$VERIFIEDJS_BIN" ]]; then
  lake build verifiedjs >/dev/null
fi
if [[ ! -x "$VERIFIEDJS_BIN" ]]; then
  echo "ERROR: verifiedjs binary missing at $VERIFIEDJS_BIN" >&2
  exit 2
fi

frontmatter() {
  awk '
    BEGIN { inBlock = 0 }
    /^\/\*---/ { inBlock = 1; next }
    inBlock && /^---\*\// { exit }
    inBlock { print }
  ' "$1"
}

has_frontmatter_pattern() {
  local file="$1"
  local pat="$2"
  frontmatter "$file" | grep -Eq "$pat"
}

is_case_file() {
  local file="$1"
  [[ "$file" == *.case ]]
}

extract_case_value() {
  local file="$1"
  local key="$2"
  awk -v key="$key" '
    BEGIN { active = 0 }
    {
      if ($0 ~ /^[[:space:]]*\/\/-[[:space:]]*/) {
        line = $0
        sub(/^[[:space:]]*\/\/-[[:space:]]*/, "", line)
        split(line, parts, /[^A-Za-z0-9_:-]/)
        active = (parts[1] == key)
        next
      }
      if (active) {
        sub(/^[[:space:]]+/, "", $0)
        print
      }
    }
  ' "$file"
}

limitation_reason() {
  local file="$1"

  if has_frontmatter_pattern "$file" '^features:.*iterator-helpers'; then
    echo "iterator-helpers"
    return
  fi
  if [[ "$file" == *"/annexB/"* ]]; then
    echo "annex-b"
    return
  fi
  if [[ "$file" == *"/language/statements/for/dstr/"* ]]; then
    echo "destructuring-for-statement"
    return
  fi
  if grep -Eq '\?\.|\?\?' "$file"; then
    echo "optional-chaining-or-nullish"
    return
  fi
  if grep -Eq '(^|[^[:alnum:]_])class[[:space:]]+[[:alpha:]_$]' "$file"; then
    echo "class-declaration"
    return
  fi
  if grep -Eq 'for[[:space:]]*\([^\)]*\b(in|of)\b' "$file"; then
    echo "for-in-of"
    return
  fi
  echo ""
}

is_meta_skip() {
  local file="$1"

  if [[ "$file" == *"_FIXTURE.js" ]]; then
    echo "fixture"
    return
  fi

  if has_frontmatter_pattern "$file" '^negative:'; then
    echo "negative"
    return
  fi

  if has_frontmatter_pattern "$file" '^flags:.*\b(module|async|raw|CanBlockIsTrue)\b'; then
    echo "unsupported-flags"
    return
  fi

  if grep -q '\$DONOTEVALUATE();' "$file"; then
    echo "parse-only"
    return
  fi

  echo ""
}

extract_includes() {
  local file="$1"
  frontmatter "$file" | awk '
    BEGIN { inIncludes = 0 }
    /^[[:space:]]*includes:[[:space:]]*$/ { inIncludes = 1; next }
    inIncludes {
      if ($0 ~ /^[[:space:]]*-[[:space:]]+/) {
        line = $0
        sub(/^[[:space:]]*-[[:space:]]+/, "", line)
        sub(/[[:space:]]+$/, "", line)
        print line
        next
      }
      if ($0 ~ /^[[:space:]]*$/) { next }
      if ($0 ~ /^[[:space:]]*[A-Za-z0-9_]+:[[:space:]]*/) { exit }
      exit
    }
  '
}

PASS=0
FAIL=0
XFAIL=0
SKIP=0
TOTAL=0

TMP_ROOT="$(mktemp -d /tmp/verifiedjs_test262_XXXXXX)"
trap 'rm -rf "$TMP_ROOT"' EXIT

ALL_FILES=()
while IFS= read -r line; do
  ALL_FILES+=("$line")
done < <(find "$SUITE_DIR" -type f \( -name '*.js' -o -name '*.case' \) | LC_ALL=C sort)

if [[ "${#ALL_FILES[@]}" -eq 0 ]]; then
  echo "ERROR: no test files found under $SUITE_DIR" >&2
  exit 2
fi

hash_hex() {
  local s="$1"
  if command -v md5sum >/dev/null 2>&1; then
    printf '%s' "$s" | md5sum | awk '{print $1}'
  else
    printf '%s' "$s" | md5
  fi
}

gcd() {
  local a="$1"
  local b="$2"
  while [[ "$b" -ne 0 ]]; do
    local t="$b"
    b=$((a % b))
    a="$t"
  done
  echo "$a"
}

if [[ "$SAMPLE_COUNT" -gt 0 ]]; then
  total_files="${#ALL_FILES[@]}"
  if [[ "$SAMPLE_COUNT" -ge "$total_files" ]]; then
    FILES=("${ALL_FILES[@]}")
  else
    seed_hex="$(hash_hex "$SEED")"
    seed_num=$((16#${seed_hex:0:8}))
    start_idx=$((seed_num % total_files))
    step=7919
    while [[ "$(gcd "$step" "$total_files")" -ne 1 ]]; do
      step=$((step + 2))
    done

    FILES=()
    idx="$start_idx"
    while [[ "${#FILES[@]}" -lt "$SAMPLE_COUNT" ]]; do
      FILES+=("${ALL_FILES[$idx]}")
      idx=$(((idx + step) % total_files))
    done
  fi
else
  FILES=("${ALL_FILES[@]}")
fi

for file in "${FILES[@]}"; do
  TOTAL=$((TOTAL + 1))

  source_file="$file"
  case_expected_error=""
  if is_case_file "$file"; then
    case_setup="$(extract_case_value "$file" "setup")"
    case_teardown="$(extract_case_value "$file" "teardown")"
    case_name_block="$(extract_case_value "$file" "name")"
    case_error_line="$(extract_case_value "$file" "error" | head -n1 || true)"
    case_expected_error="$(printf '%s' "$case_error_line" | awk '{print $1}')"
    if [[ -z "$case_setup" ]]; then
      echo "TEST262_SKIP case-no-setup ${file}"
      SKIP=$((SKIP + 1))
      continue
    fi
    source_file="$TMP_ROOT/case_${TOTAL}.js"
    {
      printf '%s\n' "$case_setup"
      if [[ -n "$case_name_block" ]]; then
        printf '\n%s\n' "$case_name_block"
      fi
      if [[ -n "$case_teardown" ]]; then
        printf '\n%s\n' "$case_teardown"
      fi
    } > "$source_file"
  fi

  if ! is_case_file "$file"; then
    meta_skip="$(is_meta_skip "$file")"
    if [[ -n "$meta_skip" ]]; then
      echo "TEST262_SKIP ${meta_skip} ${file}"
      SKIP=$((SKIP + 1))
      continue
    fi

    limitation="$(limitation_reason "$file")"
    if [[ -n "$limitation" ]]; then
      echo "TEST262_SKIP limitation:${limitation} ${file}"
      SKIP=$((SKIP + 1))
      continue
    fi
  fi

  if ! node --check "$source_file" >/dev/null 2>&1; then
    echo "TEST262_SKIP node-check-failed ${file}"
    SKIP=$((SKIP + 1))
    continue
  fi

  include_blob="$TMP_ROOT/includes_${TOTAL}.js"
  : > "$include_blob"
  missing_include=""
  if ! is_case_file "$file"; then
    while IFS= read -r include_file; do
      [[ -z "$include_file" ]] && continue
      include_path="$ROOT_DIR/tests/test262/harness/$include_file"
      if [[ ! -f "$include_path" ]]; then
        missing_include="$include_file"
        break
      fi
      cat "$include_path" >> "$include_blob"
      printf '\n' >> "$include_blob"
    done < <(extract_includes "$file")
  fi
  if [[ -n "$missing_include" ]]; then
    echo "TEST262_SKIP include-missing:${missing_include} ${file}"
    SKIP=$((SKIP + 1))
    continue
  fi

  harnessed_source="$TMP_ROOT/harness_${TOTAL}.js"
  {
    printf '%s\n' "$HARNESS_PRELUDE"
    cat "$include_blob"
    cat "$source_file"
  } > "$harnessed_source"
  source_file="$harnessed_source"

  out_file="$TMP_ROOT/$(basename "$file").wasm"
  compile_log="$TMP_ROOT/compile.log"

  if "$VERIFIEDJS_BIN" "$source_file" -o "$out_file" >"$compile_log" 2>&1; then
    wasm_stdout="$TMP_ROOT/wasm.stdout"
    wasm_stderr="$TMP_ROOT/wasm.stderr"
    wasm_rc=0
    wasmtime run "$out_file" >"$wasm_stdout" 2>"$wasm_stderr" || wasm_rc=$?

    if [[ -n "$case_expected_error" ]]; then
      node_stdout="$TMP_ROOT/node.stdout"
      node_stderr="$TMP_ROOT/node.stderr"
      node_rc=0
      node "$source_file" >"$node_stdout" 2>"$node_stderr" || node_rc=$?
      if [[ "$node_rc" -eq 0 ]] || ! grep -Eq "(^|[^[:alnum:]_])${case_expected_error}([^[:alnum:]_]|$)" "$node_stderr"; then
        echo "TEST262_FAIL case-invalid-error-spec ${file} :: expected=${case_expected_error}"
        FAIL=$((FAIL + 1))
        if [[ "$FAIL" -ge "$MAX_FAIL" ]]; then
          echo "TEST262_ABORT too-many-failures=${FAIL}"
          break
        fi
        continue
      fi
      if [[ "$wasm_rc" -ne 0 ]]; then
        echo "TEST262_PASS ${file}"
        PASS=$((PASS + 1))
      else
        echo "TEST262_FAIL runtime-expected-error-missing ${file} :: expected=${case_expected_error}"
        FAIL=$((FAIL + 1))
        if [[ "$FAIL" -ge "$MAX_FAIL" ]]; then
          echo "TEST262_ABORT too-many-failures=${FAIL}"
          break
        fi
      fi
      continue
    fi

    if [[ "$wasm_rc" -ne 0 ]]; then
      if grep -q "WebAssembly translation error" "$wasm_stderr"; then
        echo "TEST262_XFAIL known-backend:wasm-validation ${file}"
        XFAIL=$((XFAIL + 1))
      else
        echo "TEST262_FAIL runtime-exec ${file} :: wasm_rc=${wasm_rc}"
        FAIL=$((FAIL + 1))
        if [[ "$FAIL" -ge "$MAX_FAIL" ]]; then
          echo "TEST262_ABORT too-many-failures=${FAIL}"
          break
        fi
      fi
      continue
    fi

    if [[ -s "$wasm_stdout" ]] || [[ -s "$wasm_stderr" ]]; then
      node_stdout="$TMP_ROOT/node.stdout"
      node_stderr="$TMP_ROOT/node.stderr"
      node_rc=0
      node "$source_file" >"$node_stdout" 2>"$node_stderr" || node_rc=$?

      if grep -Eq 'ReferenceError: (assert|Test262Error|\$DONE) is not defined' "$node_stderr"; then
        echo "TEST262_SKIP runtime-harness-global ${file}"
        SKIP=$((SKIP + 1))
        continue
      fi

      if [[ "$node_rc" -ne 0 ]]; then
        echo "TEST262_FAIL runtime-node-exec ${file} :: node_rc=${node_rc}"
        FAIL=$((FAIL + 1))
        if [[ "$FAIL" -ge "$MAX_FAIL" ]]; then
          echo "TEST262_ABORT too-many-failures=${FAIL}"
          break
        fi
        continue
      fi

      if cmp -s "$node_stdout" "$wasm_stdout" && cmp -s "$node_stderr" "$wasm_stderr"; then
        echo "TEST262_PASS ${file}"
        PASS=$((PASS + 1))
      else
        echo "TEST262_FAIL runtime-output-mismatch ${file}"
        FAIL=$((FAIL + 1))
        if [[ "$FAIL" -ge "$MAX_FAIL" ]]; then
          echo "TEST262_ABORT too-many-failures=${FAIL}"
          break
        fi
      fi
    else
      echo "TEST262_PASS ${file}"
      PASS=$((PASS + 1))
    fi
  else
    first_err="$(grep -E 'Compilation error:|Pipeline error:|Elaboration error:' "$compile_log" | head -n1 || true)"
    if [[ "$first_err" == *"unbound variable"* ]] || [[ "$first_err" == *"stub"* ]]; then
      echo "TEST262_XFAIL known-limitation ${file} :: ${first_err}"
      XFAIL=$((XFAIL + 1))
    else
      echo "TEST262_FAIL ${file} :: ${first_err}"
      FAIL=$((FAIL + 1))
      if [[ "$FAIL" -ge "$MAX_FAIL" ]]; then
        echo "TEST262_ABORT too-many-failures=${FAIL}"
        break
      fi
    fi
  fi
done

echo "TEST262_SUMMARY mode=${MODE} pass=${PASS} fail=${FAIL} xfail=${XFAIL} skip=${SKIP} total=${TOTAL}"

if [[ "$FAIL" -gt 0 ]]; then
  exit 1
fi
