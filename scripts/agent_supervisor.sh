#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKTREE_DIR="${ROOT_DIR}/.worktrees"
LOG_ROOT="${ROOT_DIR}/agent_logs"
LOCK_DIR="${ROOT_DIR}/.agent_locks"
PROMPT_FILE="${ROOT_DIR}/README.md"
TASKS_FILE="${ROOT_DIR}/TASKS.md"
BASE_REF="origin/main"
COUNT=1
SLEEP_SECS=20
MAX_ROUNDS=0
TEST_CMD="./tests/run_tests.sh --fast"
PUSH_AFTER_RUN=1
FETCH_BEFORE_RUN=1
STOP_ON_PASS=1
DRY_RUN=0
MODE=""
MONITOR_SECS=5
CLEANUP_LOCAL=1
MERGE_LOCAL=1
KEEP_LOCAL=0
LAST_INTEGRATED=0
VALIDATOR_LLM_COUNT=2
USE_LLM_PARALLEL_PLANNER=1
PLANNER_CANDIDATE_CAP=20

SCRIPT_START_TS="$(date +%s)"
SUMMARY_PRINTED=0
TOTAL_ROUNDS=0
TOTAL_AGENTS=0
TOTAL_OK=0
TOTAL_FAIL=0
LAST_TEST_PASS="N/A"
LAST_TEST_LOG=""
LAST_VALIDATION_NOTE=""
declare -a SUMMARY_OK
declare -a SUMMARY_FAIL
declare -a ROUND_TASK_IDS
declare -a ROUND_TASK_TEXTS
declare -a CAND_TASK_LINES
declare -a CAND_TASK_IDS
declare -a CAND_TASK_TEXTS
LAST_SPAWN_PID=0

timestamp() {
  date +"%Y%m%d_%H%M%S"
}

usage() {
  cat <<'USAGE'
Usage:
  scripts/agent_supervisor.sh spawn [options]
  scripts/agent_supervisor.sh supervise [options]

Modes:
  spawn      Spawn one round of N codex subagents in parallel.
  supervise  Repeatedly spawn rounds and run a gate test after each round.

Options:
  --count N            Number of agents per round (default: 1)
  --base REF           Git ref for new worktrees (default: origin/main)
  --prompt-file PATH   Prompt source file (default: README.md)
  --tasks-file PATH    Task file to assign from (default: TASKS.md)
  --test-cmd CMD       Test command for supervise mode (default: ./tests/run_tests.sh --fast)
  --sleep SEC          Delay between rounds in supervise mode (default: 20)
  --max-rounds N       Stop after N rounds (0 = unlimited, default: 0)
  --monitor-secs N     Print agent progress every N seconds while waiting (default: 5, 0 disables)
  --validator-llms N   Number of Codex validator passes per checked task (default: 2)
  --no-llm-planner     Disable LLM planner for deciding task parallelization
  --planner-cap N      Max unchecked tasks provided to LLM planner per round (default: 20)
  --no-push            Skip pushing agent branches
  --no-merge-local     Do not merge successful local agent branches into current branch
  --keep-local         Keep local agent branches/worktrees after run (implies no cleanup)
  --cleanup-local      Force cleanup of local agent branches/worktrees even with --no-push
  --no-fetch           Skip git fetch before creating worktrees
  --no-stop-on-pass    In supervise mode, keep running even when tests pass
  --dry-run            Print planned actions only
  -h, --help           Show this help

Local task locking:
  Uses atomic mkdir locks under .agent_locks/ so parallel worktrees cannot claim
  the same TASKS.md checkbox line in a run.
USAGE
}

print_summary() {
  if [[ "${SUMMARY_PRINTED}" -eq 1 ]]; then
    return
  fi
  SUMMARY_PRINTED=1

  local elapsed
  elapsed="$(( $(date +%s) - SCRIPT_START_TS ))"

  echo ""
  echo "=== Supervisor Summary ==="
  echo "rounds=${TOTAL_ROUNDS} agents=${TOTAL_AGENTS} ok=${TOTAL_OK} fail=${TOTAL_FAIL} last_test=${LAST_TEST_PASS} elapsed=${elapsed}s"

  if [[ "${#SUMMARY_OK[@]}" -gt 0 ]]; then
    echo "completed tasks:"
    for t in "${SUMMARY_OK[@]}"; do
      echo "  - ${t}"
    done
  fi

  if [[ "${#SUMMARY_FAIL[@]}" -gt 0 ]]; then
    echo "failed tasks:"
    for t in "${SUMMARY_FAIL[@]}"; do
      echo "  - ${t}"
    done
  fi

  echo "locks dir: ${LOCK_DIR}"
  echo "logs dir: ${LOG_ROOT}"
}
trap print_summary EXIT

need_cmd() {
  local cmd="$1"
  if ! command -v "${cmd}" >/dev/null 2>&1; then
    echo "ERROR: required command not found: ${cmd}" >&2
    exit 1
  fi
}

run_or_echo() {
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    echo "[dry-run] $*"
  else
    "$@"
  fi
}

commit_supervisor_task_updates() {
  local msg="${1:-supervisor: sync task bookkeeping}"

  if [[ "${DRY_RUN}" -eq 1 ]]; then
    echo "[dry-run] git -C ${ROOT_DIR} add -- ${TASKS_FILE}"
    echo "[dry-run] git -C ${ROOT_DIR} commit -m \"${msg}\""
    return 0
  fi

  if git -C "${ROOT_DIR}" rev-parse --verify --quiet MERGE_HEAD >/dev/null; then
    echo "WARN: merge in progress; deferring task bookkeeping commit (${TASKS_FILE})" >&2
    return 1
  fi

  git -C "${ROOT_DIR}" add -- "${TASKS_FILE}" >/dev/null 2>&1 || true
  if git -C "${ROOT_DIR}" diff --cached --quiet; then
    return 0
  fi

  if git -C "${ROOT_DIR}" commit -m "${msg}" >/dev/null 2>&1; then
    echo "INFO: committed supervisor task-file updates (${TASKS_FILE})"
    return 0
  fi

  echo "WARN: failed to commit supervisor task-file updates (${TASKS_FILE})" >&2
  return 1
}

hash_text() {
  local s="$1"
  if command -v shasum >/dev/null 2>&1; then
    printf '%s' "${s}" | shasum | awk '{print substr($1,1,12)}'
  else
    printf '%s' "${s}" | cksum | awk '{print $1}'
  fi
}

slug_for_task() {
  local line_no="$1"
  local text="$2"
  local h
  h="$(hash_text "${text}")"
  echo "task_l${line_no}_${h}"
}

unchecked_tasks() {
  awk '/^- \[ \] /{txt=$0; sub(/^- \[ \] /, "", txt); print NR "|" txt}' "${TASKS_FILE}"
}

claim_task() {
  local task_id="$1"
  local task_text="$2"
  local lock_path="${LOCK_DIR}/${task_id}"

  if [[ -d "${lock_path}" ]]; then
    return 1
  fi

  if [[ "${DRY_RUN}" -eq 1 ]]; then
    return 0
  fi

  if mkdir "${lock_path}" 2>/dev/null; then
    {
      echo "status=in_progress"
      echo "task=${task_text}"
      echo "claimed_at=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
      echo "pid=$$"
    } > "${lock_path}/meta.txt"
    return 0
  fi

  return 1
}

mark_task_done() {
  local task_id="$1"
  local lock_path="${LOCK_DIR}/${task_id}"
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    return 0
  fi
  if [[ -f "${lock_path}/meta.txt" ]]; then
    sed -i.bak 's/^status=.*/status=done/' "${lock_path}/meta.txt" 2>/dev/null || true
    rm -f "${lock_path}/meta.txt.bak" 2>/dev/null || true
    echo "done_at=$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "${lock_path}/meta.txt"
  fi
}

mark_task_pending_merge() {
  local task_id="$1"
  local branch="${2:-}"
  local wt="${3:-}"
  local log_path="${4:-}"
  local lock_path="${LOCK_DIR}/${task_id}"
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    return 0
  fi
  if [[ -f "${lock_path}/meta.txt" ]]; then
    sed -i.bak 's/^status=.*/status=pending_merge/' "${lock_path}/meta.txt" 2>/dev/null || true
    rm -f "${lock_path}/meta.txt.bak" 2>/dev/null || true
    echo "pending_merge_at=$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "${lock_path}/meta.txt"
    [[ -n "${branch}" ]] && echo "branch=${branch}" >> "${lock_path}/meta.txt"
    [[ -n "${wt}" ]] && echo "worktree=${wt}" >> "${lock_path}/meta.txt"
    [[ -n "${log_path}" ]] && echo "agent_log=${log_path}" >> "${lock_path}/meta.txt"
  fi
}

read_lock_meta_value() {
  local lock_path="$1"
  local key="$2"
  sed -nE "s/^${key}=(.*)$/\\1/p" "${lock_path}/meta.txt" | tail -n1
}

set_lock_status() {
  local task_id="$1"
  local status="$2"
  local lock_path="${LOCK_DIR}/${task_id}"
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    return 0
  fi
  if [[ -f "${lock_path}/meta.txt" ]]; then
    sed -i.bak "s/^status=.*/status=${status}/" "${lock_path}/meta.txt" 2>/dev/null || true
    rm -f "${lock_path}/meta.txt.bak" 2>/dev/null || true
    echo "${status}_at=$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "${lock_path}/meta.txt"
  fi
}

merge_pending_branch_at_start() {
  local task_id="$1"
  local branch="$2"
  local log="${LOG_ROOT}/pending_merge_${task_id}_$(timestamp).log"

  echo "STARTUP_MERGE: attempting ${task_id} via ${branch} (log: ${log})"
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    return 0
  fi

  if ! git -C "${ROOT_DIR}" rev-parse --verify --quiet "${branch}^{commit}" >/dev/null; then
    echo "STARTUP_MERGE_FAIL: branch missing ${branch}" | tee -a "${log}"
    return 1
  fi

  local ahead
  ahead="$(git -C "${ROOT_DIR}" rev-list --count "HEAD..${branch}" 2>/dev/null || echo 0)"
  if [[ "${ahead}" -eq 0 ]]; then
    echo "STARTUP_MERGE_SKIP: no commits ahead on ${branch}" | tee -a "${log}"
    return 0
  fi

  if git -C "${ROOT_DIR}" merge --no-ff "${branch}" -m "Merge ${branch}"; then
    echo "STARTUP_MERGE_OK: merged ${branch}" | tee -a "${log}"
    return 0
  fi

  echo "STARTUP_MERGE_WARN: merge failed for ${branch}; invoking codex resolver" | tee -a "${log}"
  if resolve_merge_with_codex "${branch}" "${log}"; then
    echo "STARTUP_MERGE_OK: codex resolved ${branch}" | tee -a "${log}"
    return 0
  fi

  echo "STARTUP_MERGE_FAIL: unresolved ${branch}" | tee -a "${log}"
  return 1
}

resolve_pending_merges_at_start() {
  local pending_count=0
  local merged_count=0
  local unresolved_count=0

  shopt -s nullglob
  local lock_path
  for lock_path in "${LOCK_DIR}"/task_*/meta.txt; do
    local lock_dir task_id status branch
    lock_dir="$(dirname "${lock_path}")"
    task_id="$(basename "${lock_dir}")"
    status="$(read_lock_meta_value "${lock_dir}" "status")"
    [[ "${status}" != "pending_merge" ]] && continue

    pending_count=$((pending_count + 1))
    branch="$(read_lock_meta_value "${lock_dir}" "branch")"
    if [[ -z "${branch}" ]]; then
      echo "STARTUP_MERGE_WARN: ${task_id} has pending_merge but no branch metadata; leaving pending"
      unresolved_count=$((unresolved_count + 1))
      continue
    fi

    if merge_pending_branch_at_start "${task_id}" "${branch}"; then
      set_lock_status "${task_id}" "done"
      merged_count=$((merged_count + 1))
    else
      unresolved_count=$((unresolved_count + 1))
    fi
  done
  shopt -u nullglob

  if [[ "${pending_count}" -gt 0 ]]; then
    echo "STARTUP_MERGE_SUMMARY: pending=${pending_count} merged=${merged_count} unresolved=${unresolved_count}"
  fi
}

mark_task_done_in_tasks() {
  local task_id="$1"
  local task_text="$2"

  if [[ "${DRY_RUN}" -eq 1 ]]; then
    return 0
  fi

  local tmp
  tmp="$(mktemp)"
  if awk -v t="${task_text}" '
    {
      if (!changed && $0 == ("- [ ] " t)) {
        print "- [x] " t " — DONE by agent supervisor"
        changed=1
      } else {
        print
      }
    }
    END { if (!changed) exit 3 }
  ' "${TASKS_FILE}" > "${tmp}"; then
    mv "${tmp}" "${TASKS_FILE}"
  else
    rm -f "${tmp}"
    echo "WARN: could not mark task as done in ${TASKS_FILE}: ${task_id}" >&2
  fi
}

normalize_task_text() {
  local t="$1"
  printf '%s' "${t}" | sed -E 's/ — DONE by .*$//'
}

ensure_validated_tasks_section() {
  if grep -q '^## Validated Completed (Supervisor)$' "${TASKS_FILE}"; then
    return 0
  fi
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    echo "[dry-run] append validated completed section to ${TASKS_FILE}"
    return 0
  fi
  {
    echo ""
    echo "## Validated Completed (Supervisor)"
  } >> "${TASKS_FILE}"
}

list_checked_tasks_pending_validation() {
  awk '
    BEGIN { validated=0 }
    /^## Validated Completed \(Supervisor\)$/ { validated=1; next }
    !validated && /^- \[x\] / {
      txt=$0
      sub(/^- \[x\] /, "", txt)
      print txt
    }
  ' "${TASKS_FILE}"
}

task_exists_in_validated_section() {
  local task_text="$1"
  awk -v t="${task_text}" '
    BEGIN { validated=0; found=0 }
    /^## Validated Completed \(Supervisor\)$/ { validated=1; next }
    validated && /^- \[x\] / {
      txt=$0
      sub(/^- \[x\] /, "", txt)
      sub(/ — VALIDATED by supervisor.*/, "", txt)
      if (txt == t) { found=1; exit }
    }
    END { exit(found ? 0 : 1) }
  ' "${TASKS_FILE}"
}

move_checked_task_to_validated_section() {
  local raw_task_text="$1"
  local normalized_task_text="$2"
  local validated_date="$3"

  if [[ "${DRY_RUN}" -eq 1 ]]; then
    echo "[dry-run] move checked task to validated section: ${normalized_task_text}"
    return 0
  fi

  local tmp
  tmp="$(mktemp)"
  if ! awk -v t="${raw_task_text}" '
    BEGIN { validated=0; moved=0 }
    /^## Validated Completed \(Supervisor\)$/ { validated=1; print; next }
    {
      if (!validated && !moved && $0 == ("- [x] " t)) {
        moved=1
        next
      }
      print
    }
    END { if (!moved) exit 3 }
  ' "${TASKS_FILE}" > "${tmp}"; then
    rm -f "${tmp}"
    return 1
  fi
  mv "${tmp}" "${TASKS_FILE}"

  if ! task_exists_in_validated_section "${normalized_task_text}"; then
    echo "- [x] ${normalized_task_text} — VALIDATED by supervisor ${validated_date}" >> "${TASKS_FILE}"
  fi
}

reopen_checked_task_with_note() {
  local raw_task_text="$1"
  local normalized_task_text="$2"
  local note="$3"
  local cleaned_note
  cleaned_note="$(printf '%s' "${note}" | tr '\n' ' ' | sed -E 's/[[:space:]]+/ /g' | sed -E 's/^ +| +$//g' | cut -c1-240)"

  if [[ "${DRY_RUN}" -eq 1 ]]; then
    echo "[dry-run] reopen checked task with note: ${normalized_task_text} :: ${cleaned_note}"
    return 0
  fi

  local tmp
  tmp="$(mktemp)"
  if ! awk -v t="${raw_task_text}" -v n="${normalized_task_text}" -v note="${cleaned_note}" '
    BEGIN { validated=0; changed=0 }
    /^## Validated Completed \(Supervisor\)$/ { validated=1; print; next }
    {
      if (!validated && !changed && $0 == ("- [x] " t)) {
        print "- [ ] " n " — TODO(supervisor): " note
        changed=1
      } else {
        print
      }
    }
    END { if (!changed) exit 3 }
  ' "${TASKS_FILE}" > "${tmp}"; then
    rm -f "${tmp}"
    return 1
  fi
  mv "${tmp}" "${TASKS_FILE}"
}

task_marked_checked_in_active_section() {
  local task_text="$1"
  awk -v t="${task_text}" '
    BEGIN { validated=0; found=0 }
    /^## Validated Completed \(Supervisor\)$/ { validated=1; next }
    !validated && /^- \[x\] / {
      txt=$0
      sub(/^- \[x\] /, "", txt)
      if (index(txt, t) == 1) { found=1; exit }
    }
    END { exit(found ? 0 : 1) }
  ' "${TASKS_FILE}"
}

annotate_unchecked_task_needs_checkoff() {
  local task_text="$1"
  local note="agent merged code but did not mark task as [x] for supervisor validation"
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    echo "[dry-run] annotate unchecked task: ${task_text}"
    return 0
  fi
  local tmp
  tmp="$(mktemp)"
  if awk -v t="${task_text}" -v note="${note}" '
    {
      if (!changed && $0 == ("- [ ] " t)) {
        print "- [ ] " t " — TODO(supervisor): " note
        changed=1
      } else {
        print
      }
    }
    END { if (!changed) exit 3 }
  ' "${TASKS_FILE}" > "${tmp}"; then
    mv "${tmp}" "${TASKS_FILE}"
  else
    rm -f "${tmp}"
  fi
}

run_llm_validator_once() {
  local task_text="$1"
  local focus="$2"
  local log="$3"
  local tmp
  tmp="$(mktemp)"
  LAST_VALIDATION_NOTE=""

  local prompt=""
  prompt+="You are a strict task validator for VerifiedJS."$'\n'
  prompt+="Task: ${task_text}"$'\n'
  prompt+="Focus: ${focus}"$'\n'
  prompt+="Inspect repository state and decide if this task is complete."$'\n'
  prompt+="Output exactly two lines:"$'\n'
  prompt+="VERDICT: PASS or FAIL"$'\n'
  prompt+="NOTES: one short actionable sentence"$'\n'

  if ! (
    cd "${ROOT_DIR}"
    codex exec -C "${ROOT_DIR}" \
      --add-dir "${ROOT_DIR}/.git" \
      --add-dir "${ROOT_DIR}/.lake" \
      "${prompt}"
  ) >"${tmp}" 2>>"${log}"; then
    LAST_VALIDATION_NOTE="validator execution failed (${focus})"
    rm -f "${tmp}"
    return 1
  fi

  local verdict notes
  verdict="$(sed -nE 's/^VERDICT:[[:space:]]*(PASS|FAIL).*$/\1/p' "${tmp}" | tail -n1)"
  notes="$(sed -nE 's/^NOTES:[[:space:]]*//p' "${tmp}" | head -n1)"
  if [[ -z "${notes}" ]]; then
    notes="$(tail -n 3 "${tmp}" | tr '\n' ' ' | sed -E 's/[[:space:]]+/ /g' | cut -c1-180)"
  fi
  echo "LLM_VALIDATOR[${focus}] VERDICT=${verdict} NOTES=${notes}" >>"${log}"
  LAST_VALIDATION_NOTE="${notes}"
  rm -f "${tmp}"

  [[ "${verdict}" == "PASS" ]]
}

run_llm_validators_for_task() {
  local task_text="$1"
  local log="$2"
  LAST_VALIDATION_NOTE=""

  if [[ "${DRY_RUN}" -eq 1 ]]; then
    return 0
  fi
  if [[ "${VALIDATOR_LLM_COUNT}" -le 0 ]]; then
    return 0
  fi

  local failures=0
  local notes=()
  local idx=1
  while [[ "${idx}" -le "${VALIDATOR_LLM_COUNT}" ]]; do
    local focus="completeness-pass-${idx}"
    if run_llm_validator_once "${task_text}" "${focus}" "${log}"; then
      :
    else
      failures=$((failures + 1))
      notes+=("${LAST_VALIDATION_NOTE}")
    fi
    idx=$((idx + 1))
  done

  if [[ "${failures}" -eq 0 ]]; then
    return 0
  fi

  LAST_VALIDATION_NOTE="$(printf '%s; ' "${notes[@]}" | sed -E 's/; $//')"
  return 1
}

review_checked_tasks_with_validators() {
  local round="$1"
  local review_log="${LOG_ROOT}/validator_round_${round}_$(timestamp).log"

  ensure_validated_tasks_section
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    echo "ROUND ${round}: [dry-run] validating checked tasks via symbolic + LLM validators"
    return 0
  fi

  echo "ROUND ${round}: validating checked tasks (log: ${review_log})"

  local reviewed=0
  while IFS= read -r raw_task_text; do
    [[ -z "${raw_task_text}" ]] && continue
    reviewed=$((reviewed + 1))

    local normalized_task_text
    normalized_task_text="$(normalize_task_text "${raw_task_text}")"
    if task_exists_in_validated_section "${normalized_task_text}"; then
      continue
    fi

    local fail_note=""
    if ! run_task_symbolic_validation "${normalized_task_text}" "${ROOT_DIR}" "${review_log}"; then
      fail_note="symbolic checks failed"
    elif ! run_llm_validators_for_task "${normalized_task_text}" "${review_log}"; then
      fail_note="${LAST_VALIDATION_NOTE}"
    fi

    if [[ -z "${fail_note}" ]]; then
      if move_checked_task_to_validated_section "${raw_task_text}" "${normalized_task_text}" "$(date -u +%Y-%m-%d)"; then
        echo "VALIDATED_TASK: ${normalized_task_text}" | tee -a "${review_log}"
      else
        echo "WARN: could not move checked task to validated section: ${raw_task_text}" | tee -a "${review_log}"
      fi
    else
      if reopen_checked_task_with_note "${raw_task_text}" "${normalized_task_text}" "${fail_note}"; then
        echo "REOPEN_TASK: ${normalized_task_text} :: ${fail_note}" | tee -a "${review_log}"
      else
        echo "WARN: could not reopen failed checked task: ${raw_task_text}" | tee -a "${review_log}"
      fi
    fi
  done < <(list_checked_tasks_pending_validation)

  echo "ROUND ${round}: validator review processed ${reviewed} checked task(s)"
  return 0
}

release_task_lock() {
  local task_id="$1"
  local lock_path="${LOCK_DIR}/${task_id}"
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    return 0
  fi
  rm -rf "${lock_path}"
}

file_has_sorry() {
  local file="$1"
  rg -n "sorry" "${file}" >/dev/null 2>&1
}

run_validation_cmd() {
  local wt="$1"
  local log="$2"
  local label="$3"
  local cmd="$4"

  echo "VALIDATE: ${label}"
  echo "VALIDATE: ${label}" >>"${log}"
  echo "  cmd: ${cmd}" >>"${log}"

  if (cd "${wt}" && bash -lc "${cmd}") >>"${log}" 2>&1; then
    return 0
  fi
  echo "VALIDATE_FAIL: ${label}" | tee -a "${log}"
  return 1
}

run_task_symbolic_validation() {
  local task_text="$1"
  local wt="$2"
  local log="$3"

  local t
  t="$(printf '%s' "${task_text}" | tr '[:upper:]' '[:lower:]')"

  echo "VALIDATE: selecting symbolic gates for task: ${task_text}" >>"${log}"

  # Phase 0: Parser / Lexer / AST
  if [[ "${t}" == *"parser milestone: parse"* ]] || [[ "${t}" == *"parse ≥95%"* ]] || [[ "${t}" == *"parse >=95%"* ]]; then
    run_validation_cmd "${wt}" "${log}" "parser full flagship fail-fast gate" "./scripts/parse_flagship_failfast.sh --full" || return 1
    return 0
  fi
  if [[ "${t}" == *"js.source.parser"* ]] || [[ "${t}" == *"js.source.lexer"* ]] || [[ "${t}" == *"js.source.ast"* ]] || [[ "${t}" == *"parser"* ]] || [[ "${t}" == *"lexer"* ]]; then
    run_validation_cmd "${wt}" "${log}" "parser smoke gate prettier" "./scripts/parse_flagship_failfast.sh --project prettier --sample-per-project 200" || return 1
    run_validation_cmd "${wt}" "${log}" "parser smoke gate babel" "./scripts/parse_flagship_failfast.sh --project babel --sample-per-project 200" || return 1
    run_validation_cmd "${wt}" "${log}" "parser smoke gate TypeScript" "./scripts/parse_flagship_failfast.sh --project TypeScript --sample-per-project 200" || return 1
  fi

  # Phase 1/2 interfaces and implementations.
  case "${t}" in
    *"js.core.syntax"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Core.Syntax" "lake build VerifiedJS.Core.Syntax" || return 1
      ;;
    *"js.core.semantics"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Core.Semantics" "lake build VerifiedJS.Core.Semantics" || return 1
      file_has_sorry "${wt}/VerifiedJS/Core/Semantics.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Core/Semantics.lean" | tee -a "${log}"; return 1; }
      ;;
    *"js.flat.syntax"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Flat.Syntax" "lake build VerifiedJS.Flat.Syntax" || return 1
      ;;
    *"js.anf.syntax"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.ANF.Syntax" "lake build VerifiedJS.ANF.Syntax" || return 1
      ;;
    *"wasm.syntax"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Wasm.Syntax" "lake build VerifiedJS.Wasm.Syntax" || return 1
      ;;
    *"core.elaborate"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Core.Elaborate" "lake build VerifiedJS.Core.Elaborate" || return 1
      file_has_sorry "${wt}/VerifiedJS/Core/Elaborate.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Core/Elaborate.lean" | tee -a "${log}"; return 1; }
      ;;
    *"flat.closureconvert"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Flat.ClosureConvert" "lake build VerifiedJS.Flat.ClosureConvert" || return 1
      file_has_sorry "${wt}/VerifiedJS/Flat/ClosureConvert.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Flat/ClosureConvert.lean" | tee -a "${log}"; return 1; }
      ;;
    *"anf.convert"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.ANF.Convert" "lake build VerifiedJS.ANF.Convert" || return 1
      file_has_sorry "${wt}/VerifiedJS/ANF/Convert.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/ANF/Convert.lean" | tee -a "${log}"; return 1; }
      ;;
    *"wasm.lower"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Wasm.Lower" "lake build VerifiedJS.Wasm.Lower" || return 1
      file_has_sorry "${wt}/VerifiedJS/Wasm/Lower.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Wasm/Lower.lean" | tee -a "${log}"; return 1; }
      ;;
    *"wasm.emit"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Wasm.Emit" "lake build VerifiedJS.Wasm.Emit" || return 1
      file_has_sorry "${wt}/VerifiedJS/Wasm/Emit.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Wasm/Emit.lean" | tee -a "${log}"; return 1; }
      ;;
    *"wasm.binary"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Wasm.Binary" "lake build VerifiedJS.Wasm.Binary" || return 1
      file_has_sorry "${wt}/VerifiedJS/Wasm/Binary.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Wasm/Binary.lean" | tee -a "${log}"; return 1; }
      ;;
    *"core.interp"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Core.Interp" "lake build VerifiedJS.Core.Interp" || return 1
      file_has_sorry "${wt}/VerifiedJS/Core/Interp.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Core/Interp.lean" | tee -a "${log}"; return 1; }
      ;;
    *"flat.interp"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Flat.Interp" "lake build VerifiedJS.Flat.Interp" || return 1
      file_has_sorry "${wt}/VerifiedJS/Flat/Interp.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Flat/Interp.lean" | tee -a "${log}"; return 1; }
      ;;
    *"anf.interp"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.ANF.Interp" "lake build VerifiedJS.ANF.Interp" || return 1
      file_has_sorry "${wt}/VerifiedJS/ANF/Interp.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/ANF/Interp.lean" | tee -a "${log}"; return 1; }
      ;;
    *"wasm.ir.interp"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Wasm.IRInterp" "lake build VerifiedJS.Wasm.IRInterp" || return 1
      file_has_sorry "${wt}/VerifiedJS/Wasm/IRInterp.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Wasm/IRInterp.lean" | tee -a "${log}"; return 1; }
      ;;
    *"core.print"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Core.Print" "lake build VerifiedJS.Core.Print" || return 1
      file_has_sorry "${wt}/VerifiedJS/Core/Print.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Core/Print.lean" | tee -a "${log}"; return 1; }
      ;;
    *"flat.print"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Flat.Print" "lake build VerifiedJS.Flat.Print" || return 1
      file_has_sorry "${wt}/VerifiedJS/Flat/Print.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Flat/Print.lean" | tee -a "${log}"; return 1; }
      ;;
    *"anf.print"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.ANF.Print" "lake build VerifiedJS.ANF.Print" || return 1
      file_has_sorry "${wt}/VerifiedJS/ANF/Print.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/ANF/Print.lean" | tee -a "${log}"; return 1; }
      ;;
    *"wasm.print"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Wasm.Print" "lake build VerifiedJS.Wasm.Print" || return 1
      file_has_sorry "${wt}/VerifiedJS/Wasm/Print.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Wasm/Print.lean" | tee -a "${log}"; return 1; }
      ;;
    *"wasm.ir.print"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Wasm.IRPrint" "lake build VerifiedJS.Wasm.IRPrint" || return 1
      file_has_sorry "${wt}/VerifiedJS/Wasm/IRPrint.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Wasm/IRPrint.lean" | tee -a "${log}"; return 1; }
      ;;
    *"flat.semantics"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Flat.Semantics" "lake build VerifiedJS.Flat.Semantics" || return 1
      file_has_sorry "${wt}/VerifiedJS/Flat/Semantics.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Flat/Semantics.lean" | tee -a "${log}"; return 1; }
      ;;
    *"anf.semantics"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.ANF.Semantics" "lake build VerifiedJS.ANF.Semantics" || return 1
      file_has_sorry "${wt}/VerifiedJS/ANF/Semantics.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/ANF/Semantics.lean" | tee -a "${log}"; return 1; }
      ;;
    *"wasm.semantics"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Wasm.Semantics" "lake build VerifiedJS.Wasm.Semantics" || return 1
      file_has_sorry "${wt}/VerifiedJS/Wasm/Semantics.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Wasm/Semantics.lean" | tee -a "${log}"; return 1; }
      ;;
    *"elaboratecorrect"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Proofs.ElaborateCorrect" "lake build VerifiedJS.Proofs.ElaborateCorrect" || return 1
      file_has_sorry "${wt}/VerifiedJS/Proofs/ElaborateCorrect.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Proofs/ElaborateCorrect.lean" | tee -a "${log}"; return 1; }
      ;;
    *"closureconvertcorrect"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Proofs.ClosureConvertCorrect" "lake build VerifiedJS.Proofs.ClosureConvertCorrect" || return 1
      file_has_sorry "${wt}/VerifiedJS/Proofs/ClosureConvertCorrect.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Proofs/ClosureConvertCorrect.lean" | tee -a "${log}"; return 1; }
      ;;
    *"anfconvertcorrect"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Proofs.ANFConvertCorrect" "lake build VerifiedJS.Proofs.ANFConvertCorrect" || return 1
      file_has_sorry "${wt}/VerifiedJS/Proofs/ANFConvertCorrect.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Proofs/ANFConvertCorrect.lean" | tee -a "${log}"; return 1; }
      ;;
    *"lowercorrect"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Proofs.LowerCorrect" "lake build VerifiedJS.Proofs.LowerCorrect" || return 1
      file_has_sorry "${wt}/VerifiedJS/Proofs/LowerCorrect.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Proofs/LowerCorrect.lean" | tee -a "${log}"; return 1; }
      ;;
    *"emitcorrect"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Proofs.EmitCorrect" "lake build VerifiedJS.Proofs.EmitCorrect" || return 1
      file_has_sorry "${wt}/VerifiedJS/Proofs/EmitCorrect.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Proofs/EmitCorrect.lean" | tee -a "${log}"; return 1; }
      ;;
    *"endtoend"*|*"compose endtoend.lean"*)
      run_validation_cmd "${wt}" "${log}" "build VerifiedJS.Proofs.EndToEnd" "lake build VerifiedJS.Proofs.EndToEnd" || return 1
      file_has_sorry "${wt}/VerifiedJS/Proofs/EndToEnd.lean" && { echo "VALIDATE_FAIL: sorry remains in VerifiedJS/Proofs/EndToEnd.lean" | tee -a "${log}"; return 1; }
      ;;
  esac

  return 0
}

parse_args() {
  MODE="${1:-}"
  if [[ -z "${MODE}" || "${MODE}" == "-h" || "${MODE}" == "--help" ]]; then
    usage
    exit 0
  fi
  shift || true

  while [[ $# -gt 0 ]]; do
    case "$1" in
      --count)
        COUNT="${2:?missing value for --count}"
        shift 2
        ;;
      --base)
        BASE_REF="${2:?missing value for --base}"
        shift 2
        ;;
      --prompt-file)
        PROMPT_FILE="${2:?missing value for --prompt-file}"
        shift 2
        ;;
      --tasks-file)
        TASKS_FILE="${2:?missing value for --tasks-file}"
        shift 2
        ;;
      --test-cmd)
        TEST_CMD="${2:?missing value for --test-cmd}"
        shift 2
        ;;
      --sleep)
        SLEEP_SECS="${2:?missing value for --sleep}"
        shift 2
        ;;
      --max-rounds)
        MAX_ROUNDS="${2:?missing value for --max-rounds}"
        shift 2
        ;;
      --monitor-secs)
        MONITOR_SECS="${2:?missing value for --monitor-secs}"
        shift 2
        ;;
      --validator-llms)
        VALIDATOR_LLM_COUNT="${2:?missing value for --validator-llms}"
        shift 2
        ;;
      --no-llm-planner)
        USE_LLM_PARALLEL_PLANNER=0
        shift
        ;;
      --planner-cap)
        PLANNER_CANDIDATE_CAP="${2:?missing value for --planner-cap}"
        shift 2
        ;;
      --no-push)
        PUSH_AFTER_RUN=0
        shift
        ;;
      --no-merge-local)
        MERGE_LOCAL=0
        shift
        ;;
      --keep-local)
        KEEP_LOCAL=1
        CLEANUP_LOCAL=0
        shift
        ;;
      --cleanup-local)
        CLEANUP_LOCAL=1
        KEEP_LOCAL=0
        shift
        ;;
      --no-fetch)
        FETCH_BEFORE_RUN=0
        shift
        ;;
      --no-stop-on-pass)
        STOP_ON_PASS=0
        shift
        ;;
      --dry-run)
        DRY_RUN=1
        shift
        ;;
      -h|--help)
        usage
        exit 0
        ;;
      *)
        echo "ERROR: unknown option: $1" >&2
        usage
        exit 1
        ;;
    esac
  done

  if [[ "${MODE}" != "spawn" && "${MODE}" != "supervise" ]]; then
    echo "ERROR: mode must be 'spawn' or 'supervise'" >&2
    usage
    exit 1
  fi
}

setup() {
  need_cmd git
  need_cmd codex
  mkdir -p "${WORKTREE_DIR}" "${LOG_ROOT}" "${LOCK_DIR}"

  if [[ ! -f "${PROMPT_FILE}" ]]; then
    echo "ERROR: prompt file not found: ${PROMPT_FILE}" >&2
    exit 1
  fi
  if [[ ! -f "${TASKS_FILE}" ]]; then
    echo "ERROR: tasks file not found: ${TASKS_FILE}" >&2
    exit 1
  fi

  if [[ "${FETCH_BEFORE_RUN}" -eq 1 && "${DRY_RUN}" -eq 0 ]]; then
    if ! git -C "${ROOT_DIR}" fetch origin main >/dev/null 2>&1; then
      echo "WARN: git fetch origin main failed; continuing with local refs"
    fi
  elif [[ "${FETCH_BEFORE_RUN}" -eq 1 ]]; then
    echo "[dry-run] git -C ${ROOT_DIR} fetch origin main"
  fi

  resolve_base_ref
  resolve_pending_merges_at_start
  commit_supervisor_task_updates "supervisor: reconcile pending merges at startup" || true
}

resolve_base_ref() {
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    return 0
  fi

  if git -C "${ROOT_DIR}" rev-parse --verify --quiet "${BASE_REF}^{commit}" >/dev/null; then
    return 0
  fi

  local fallback=""
  if git -C "${ROOT_DIR}" rev-parse --verify --quiet "main^{commit}" >/dev/null; then
    fallback="main"
  elif git -C "${ROOT_DIR}" rev-parse --verify --quiet "master^{commit}" >/dev/null; then
    fallback="master"
  else
    fallback="HEAD"
  fi

  echo "WARN: base ref '${BASE_REF}' not found; falling back to '${fallback}'"
  BASE_REF="${fallback}"
}

create_worktree() {
  local round="$1"
  local index="$2"
  local task_id="$3"

  local run_id
  run_id="$(timestamp)_r${round}_a${index}_$RANDOM"
  local branch="codex/agent_${run_id}"
  local wt="${WORKTREE_DIR}/agent_${run_id}"
  local log="${LOG_ROOT}/agent_${run_id}.log"

  if [[ "${DRY_RUN}" -eq 1 ]]; then
    echo "[dry-run] git -C ${ROOT_DIR} worktree add -b ${branch} ${wt} ${BASE_REF}" >&2
  else
    if ! git -C "${ROOT_DIR}" worktree add -b "${branch}" "${wt}" "${BASE_REF}" >/dev/null; then
      echo "ERROR: failed to create worktree for ${branch} from ${BASE_REF}" >&2
      return 1
    fi
    # Reuse root dependency cache so agents don't re-fetch Lake deps per worktree.
    if [[ -d "${ROOT_DIR}/.lake" && ! -e "${wt}/.lake" ]]; then
      ln -s "${ROOT_DIR}/.lake" "${wt}/.lake" 2>/dev/null || true
    fi
  fi

  echo "${run_id}|${branch}|${wt}|${log}|${task_id}"
}

spawn_codex_bg() {
  local wt="$1"
  local log="$2"
  local task_text="$3"
  local prompt

  prompt="$(cat "${PROMPT_FILE}")"
  prompt+=$'\n\n'
  prompt+="Assigned task: ${task_text}"$'\n'
  prompt+="Use this exact assigned task. Do NOT self-claim from TASKS.md or current_tasks/."$'\n'
  prompt+="Mark your assigned task as [x] in TASKS.md when you believe it is complete. Keep it in-place; supervisor validators will relocate validated tasks."$'\n'
  prompt+="Implement the task, run ./tests/run_tests.sh --fast, commit your changes, and exit."$'\n'
  prompt+="If you hit recurring Lean errors or workflow pitfalls, append a concise entry to MEMORY/AGENTS.md (symptom -> fix -> guardrail)."$'\n'
  prompt+="Prune low-value or stale tips in MEMORY/AGENTS.md; keep only high-signal guidance."$'\n'
  if [[ "${task_text}" =~ [Pp]arser|[Pp]arse|[Ll]exer|[Aa][Ss][Tt] ]]; then
    prompt+="This task touches parsing/lexing/AST. Run parser fail-fast gates before commit:"$'\n'
    prompt+="1) quick project-by-project smoke gate (heaviest last):"$'\n'
    prompt+="   ./scripts/parse_flagship_failfast.sh --project prettier --sample-per-project 200"$'\n'
    prompt+="   ./scripts/parse_flagship_failfast.sh --project babel --sample-per-project 200"$'\n'
    prompt+="   ./scripts/parse_flagship_failfast.sh --project TypeScript --sample-per-project 200"$'\n'
    prompt+="2) when near-done or fixing parser regressions: ./scripts/parse_flagship_failfast.sh --full"$'\n'
    prompt+="If parser gate fails, fix or add a TODO task describing the blocker before exit."$'\n'
  fi

  if [[ "${DRY_RUN}" -eq 1 ]]; then
    echo "[dry-run] codex exec -C ${wt} --add-dir ${ROOT_DIR}/.git --add-dir ${ROOT_DIR}/.lake <prompt with assigned task> > ${log}"
    LAST_SPAWN_PID=0
    return 0
  fi

  (
    cd "${ROOT_DIR}"
    codex exec -C "${wt}" \
      --add-dir "${ROOT_DIR}/.git" \
      --add-dir "${ROOT_DIR}/.lake" \
      "${prompt}"
  ) >"${log}" 2>&1 &

  LAST_SPAWN_PID=$!
  return 0
}

push_and_cleanup() {
  local branch="$1"
  local wt="$2"
  local log="$3"
  local st="${4:-0}"
  local merged=0
  LAST_INTEGRATED=0

  if [[ "${DRY_RUN}" -eq 1 ]]; then
    if [[ "${st}" -eq 0 ]]; then
      LAST_INTEGRATED=1
    fi
  fi

  if [[ "${PUSH_AFTER_RUN}" -eq 0 && "${MERGE_LOCAL}" -eq 1 && "${st}" -eq 0 && "${DRY_RUN}" -eq 0 ]]; then
    local ahead
    ahead="$(git -C "${ROOT_DIR}" rev-list --count "HEAD..${branch}" 2>/dev/null || echo 0)"
    if [[ "${ahead}" -gt 0 ]]; then
      if git -C "${ROOT_DIR}" merge --no-ff "${branch}" -m "Merge ${branch}"; then
        merged=1
        LAST_INTEGRATED=1
        echo "INFO: merged ${branch} into $(git -C "${ROOT_DIR}" branch --show-current)" >>"${log}"
      else
        echo "WARN: merge command failed for ${branch}; invoking codex for conflict resolution" >>"${log}"
        if resolve_merge_with_codex "${branch}" "${log}"; then
          merged=1
          LAST_INTEGRATED=1
          echo "INFO: codex resolved merge for ${branch}" >>"${log}"
        else
          echo "WARN: codex could not resolve merge for ${branch}; keeping branch/worktree for manual resolve" >>"${log}"
          echo "WARN: merge unresolved for ${branch}; retained ${wt}"
          return 0
        fi
      fi
    fi
  fi

  if [[ "${KEEP_LOCAL}" -eq 1 ]]; then
    echo "INFO: retained local branch/worktree for merge: ${branch} (${wt})" >>"${log}"
    echo "INFO: retained ${branch} at ${wt} (no-push mode)"
    return 0
  fi

  if [[ "${DRY_RUN}" -eq 0 ]] && ! git -C "${ROOT_DIR}" worktree list --porcelain | grep -Fq "worktree ${wt}"; then
    echo "WARN: skipping cleanup for missing worktree ${wt}" >>"${log}"
    return 0
  fi

  if [[ "${PUSH_AFTER_RUN}" -eq 1 ]]; then
    if [[ "${DRY_RUN}" -eq 1 ]]; then
      echo "[dry-run] git -C ${wt} push -u origin ${branch}"
    else
      git -C "${wt}" push -u origin "${branch}" >>"${log}" 2>&1 || true
    fi
  fi

  if [[ "${PUSH_AFTER_RUN}" -eq 0 && "${MERGE_LOCAL}" -eq 1 && "${merged}" -eq 0 ]]; then
    echo "INFO: local merge not performed for ${branch}" >>"${log}"
  fi

  if [[ "${CLEANUP_LOCAL}" -eq 0 ]]; then
    return 0
  fi

  run_or_echo git -C "${ROOT_DIR}" worktree remove "${wt}" --force
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    echo "[dry-run] git -C ${ROOT_DIR} branch -D ${branch}"
  else
    git -C "${ROOT_DIR}" branch -D "${branch}" >/dev/null 2>&1 || true
  fi
}

resolve_merge_with_codex() {
  local branch="$1"
  local log="$2"

  if [[ "${DRY_RUN}" -eq 1 ]]; then
    return 0
  fi

  local prompt=""
  prompt+="A git merge of branch '${branch}' is currently in progress in this repository and has conflicts or unresolved merge state."$'\n'
  prompt+="Resolve all merge issues now using this workspace, preserving both sides' intent, then complete the merge commit."$'\n'
  prompt+="Requirements:"$'\n'
  prompt+="- Do not abort the merge."$'\n'
  prompt+="- Stage resolved files and finish with a merge commit."$'\n'
  prompt+="- Keep changes minimal and compile/test-safe when possible."$'\n'
  prompt+="- Exit non-zero only if you cannot complete the merge."$'\n'

  echo "INFO: running codex merge resolver for ${branch} (log: ${log})"
  if ! (
    cd "${ROOT_DIR}"
    codex exec -C "${ROOT_DIR}" \
      --add-dir "${ROOT_DIR}/.git" \
      --add-dir "${ROOT_DIR}/.lake" \
      "${prompt}" 2>&1 | tee -a "${log}"
  ); then
    return 1
  fi

  if git -C "${ROOT_DIR}" rev-parse --verify --quiet MERGE_HEAD >/dev/null; then
    return 1
  fi
  return 0
}

record_test_failure_todo() {
  local round="$1"
  local sup_log="$2"
  local todo
  todo="- [ ] Investigate supervisor test-gate failure after round ${round} (`${TEST_CMD}`); see ${sup_log}"

  if grep -Fqx "${todo}" "${TASKS_FILE}"; then
    echo "ROUND ${round}: todo already exists for this failing test gate"
    return 0
  fi

  echo "${todo}" >> "${TASKS_FILE}"
  git -C "${ROOT_DIR}" add "${TASKS_FILE}" >/dev/null 2>&1 || true
  if git -C "${ROOT_DIR}" diff --cached --quiet; then
    return 0
  fi
  git -C "${ROOT_DIR}" commit -m "supervisor: add TODO for failing test gate (round ${round})" >/dev/null 2>&1 || true
  echo "ROUND ${round}: added TODO to ${TASKS_FILE} and committed"
}

task_is_blocker_text() {
  local task_text="$1"
  local t
  t="$(printf '%s' "${task_text}" | tr '[:upper:]' '[:lower:]')"
  [[ "${t}" == *"implement js.source.parser"* ]] \
    || [[ "${t}" == *"implement js.source.lexer"* ]] \
    || [[ "${t}" == *"parser milestone"* ]] \
    || [[ "${t}" == *"define js.core.semantics"* ]] \
    || [[ "${t}" == *"define flat.semantics"* ]] \
    || [[ "${t}" == *"define anf.semantics"* ]] \
    || [[ "${t}" == *"define wasm.semantics"* ]]
}

gather_candidate_tasks() {
  local cap="$1"
  CAND_TASK_LINES=()
  CAND_TASK_IDS=()
  CAND_TASK_TEXTS=()

  local seen=0
  while IFS='|' read -r line_no task_text; do
    local task_id
    task_id="$(slug_for_task "${line_no}" "${task_text}")"
    if [[ -d "${LOCK_DIR}/${task_id}" ]]; then
      continue
    fi
    CAND_TASK_LINES+=("${line_no}")
    CAND_TASK_IDS+=("${task_id}")
    CAND_TASK_TEXTS+=("${task_text}")
    seen=$((seen + 1))
    if [[ "${cap}" -gt 0 && "${seen}" -ge "${cap}" ]]; then
      break
    fi
  done < <(unchecked_tasks)
}

candidate_text_for_id() {
  local id="$1"
  for i in "${!CAND_TASK_IDS[@]}"; do
    if [[ "${CAND_TASK_IDS[$i]}" == "${id}" ]]; then
      printf '%s' "${CAND_TASK_TEXTS[$i]}"
      return 0
    fi
  done
  return 1
}

plan_parallel_tasks_with_llm() {
  local needed="$1"
  local plan_log="$2"
  local selected_file
  selected_file="$(mktemp)"

  if [[ "${#CAND_TASK_IDS[@]}" -eq 0 ]]; then
    rm -f "${selected_file}"
    return 1
  fi

  local prompt=""
  prompt+="You are scheduling Codex agents for VerifiedJS."$'\n'
  prompt+="Choose which tasks can run in parallel this round."$'\n'
  prompt+="Constraints:"$'\n'
  prompt+="- Output only lines in format: SELECT <task_id>"$'\n'
  prompt+="- Output at least 1 and at most ${needed} SELECT lines."$'\n'
  prompt+="- Prefer a single task when there is a clear blocker (parser/lexer/parser milestone/semantics foundation)."$'\n'
  prompt+="- Otherwise maximize safe parallelism while avoiding dependent tasks in the same phase."$'\n'
  prompt+="Candidates:"$'\n'
  for i in "${!CAND_TASK_IDS[@]}"; do
    prompt+="- ${CAND_TASK_IDS[$i]} :: ${CAND_TASK_TEXTS[$i]}"$'\n'
  done

  if ! (
    cd "${ROOT_DIR}"
    codex exec -C "${ROOT_DIR}" \
      --add-dir "${ROOT_DIR}/.git" \
      --add-dir "${ROOT_DIR}/.lake" \
      "${prompt}"
  ) >"${selected_file}" 2>>"${plan_log}"; then
    rm -f "${selected_file}"
    return 1
  fi

  ROUND_TASK_IDS=()
  ROUND_TASK_TEXTS=()
  while IFS= read -r line; do
    if [[ "${line}" =~ ^SELECT[[:space:]]+([A-Za-z0-9_]+)$ ]]; then
      local id="${BASH_REMATCH[1]}"
      local txt
      txt="$(candidate_text_for_id "${id}" || true)"
      if [[ -n "${txt}" ]]; then
        ROUND_TASK_IDS+=("${id}")
        ROUND_TASK_TEXTS+=("${txt}")
        if [[ "${#ROUND_TASK_IDS[@]}" -ge "${needed}" ]]; then
          break
        fi
      fi
    fi
  done < "${selected_file}"
  rm -f "${selected_file}"

  [[ "${#ROUND_TASK_IDS[@]}" -gt 0 ]]
}

plan_parallel_tasks_heuristic() {
  local needed="$1"
  ROUND_TASK_IDS=()
  ROUND_TASK_TEXTS=()

  if [[ "${#CAND_TASK_IDS[@]}" -eq 0 ]]; then
    return 1
  fi

  # If first available task is a blocker, focus with a single agent.
  if task_is_blocker_text "${CAND_TASK_TEXTS[0]}"; then
    ROUND_TASK_IDS+=("${CAND_TASK_IDS[0]}")
    ROUND_TASK_TEXTS+=("${CAND_TASK_TEXTS[0]}")
    return 0
  fi

  local picked=0
  for i in "${!CAND_TASK_IDS[@]}"; do
    ROUND_TASK_IDS+=("${CAND_TASK_IDS[$i]}")
    ROUND_TASK_TEXTS+=("${CAND_TASK_TEXTS[$i]}")
    picked=$((picked + 1))
    if [[ "${picked}" -ge "${needed}" ]]; then
      break
    fi
  done
  return 0
}

collect_assignments() {
  local needed="$1"
  ROUND_TASK_IDS=()
  ROUND_TASK_TEXTS=()

  gather_candidate_tasks "${PLANNER_CANDIDATE_CAP}"
  if [[ "${#CAND_TASK_IDS[@]}" -eq 0 ]]; then
    return 0
  fi

  local planner_log="${LOG_ROOT}/planner_$(timestamp).log"
  if [[ "${USE_LLM_PARALLEL_PLANNER}" -eq 1 && "${DRY_RUN}" -eq 0 ]]; then
    if plan_parallel_tasks_with_llm "${needed}" "${planner_log}"; then
      echo "PLANNER: LLM selected ${#ROUND_TASK_IDS[@]} task(s) (log: ${planner_log})"
    else
      echo "PLANNER: LLM planner failed or produced empty selection; using heuristic fallback"
      plan_parallel_tasks_heuristic "${needed}" || true
    fi
  else
    plan_parallel_tasks_heuristic "${needed}" || true
  fi

  # Claim selected tasks; if any claim fails due to race, skip it.
  local -a selected_ids=("${ROUND_TASK_IDS[@]}")
  local -a selected_texts=("${ROUND_TASK_TEXTS[@]}")
  ROUND_TASK_IDS=()
  ROUND_TASK_TEXTS=()
  for i in "${!selected_ids[@]}"; do
    local tid="${selected_ids[$i]}"
    local ttxt="${selected_texts[$i]}"
    if claim_task "${tid}" "${ttxt}"; then
      ROUND_TASK_IDS+=("${tid}")
      ROUND_TASK_TEXTS+=("${ttxt}")
    fi
  done
}

spawn_round() {
  local round="$1"
  TOTAL_ROUNDS=$((TOTAL_ROUNDS + 1))

  collect_assignments "${COUNT}"

  local assigned="${#ROUND_TASK_IDS[@]}"
  if [[ "${assigned}" -eq 0 ]]; then
    echo "ROUND ${round}: no unlocked unchecked tasks found in ${TASKS_FILE}"
    return 2
  fi

  echo "ROUND ${round}: assigned ${assigned} task(s)"
  for i in "${!ROUND_TASK_IDS[@]}"; do
    echo "  - ${ROUND_TASK_IDS[$i]} :: ${ROUND_TASK_TEXTS[$i]}"
  done

  local -a meta=()
  local -a meta_task_texts=()
  local -a pids=()
  local -a statuses=()

  echo "ROUND ${round}: creating ${assigned} worktree(s) from ${BASE_REF}"
  for i in $(seq 1 "${assigned}"); do
    local task_text_i="${ROUND_TASK_TEXTS[$((i-1))]}"
    if entry="$(create_worktree "${round}" "${i}" "${ROUND_TASK_IDS[$((i-1))]}")"; then
      meta+=( "${entry}" )
      meta_task_texts+=( "${task_text_i}" )
    else
      local failed_task_id="${ROUND_TASK_IDS[$((i-1))]}"
      TOTAL_FAIL=$((TOTAL_FAIL + 1))
      SUMMARY_FAIL+=( "${task_text_i}" )
      release_task_lock "${failed_task_id}"
    fi
  done

  if [[ "${#meta[@]}" -eq 0 ]]; then
    echo "ROUND ${round}: no worktrees created; aborting round."
    return 2
  fi

  echo "ROUND ${round}: launching codex subagents"
  for i in "${!meta[@]}"; do
    IFS='|' read -r _run_id _branch wt log _task_id <<<"${meta[$i]}"
    if spawn_codex_bg "${wt}" "${log}" "${meta_task_texts[$i]}"; then
      pids+=("${LAST_SPAWN_PID}")
    else
      pids+=("0")
    fi
  done

  echo "ROUND ${round}: waiting for ${#pids[@]} agent(s)"
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    for _ in "${pids[@]}"; do
      statuses+=("0")
    done
  else
    local remaining="${#pids[@]}"
    local last_report_ts
    last_report_ts="$(date +%s)"
    for _ in "${pids[@]}"; do
      statuses+=("__pending__")
    done

    while [[ "${remaining}" -gt 0 ]]; do
      for idx in "${!pids[@]}"; do
        if [[ "${statuses[$idx]}" != "__pending__" ]]; then
          continue
        fi
        local pid="${pids[$idx]}"
        if [[ "${pid}" == "0" ]]; then
          statuses[$idx]="1"
          remaining=$((remaining - 1))
          continue
        fi
        if kill -0 "${pid}" 2>/dev/null; then
          continue
        fi
        local st=0
        if wait "${pid}" 2>/dev/null; then
          st=0
        else
          st=$?
        fi
        statuses[$idx]="${st}"
        remaining=$((remaining - 1))
      done

      if [[ "${remaining}" -eq 0 ]]; then
        break
      fi

      if [[ "${MONITOR_SECS}" -gt 0 ]]; then
        local now_ts
        now_ts="$(date +%s)"
        if (( now_ts - last_report_ts >= MONITOR_SECS )); then
          local done_count=0
          for st in "${statuses[@]}"; do
            if [[ "${st}" != "__pending__" ]]; then
              done_count=$((done_count + 1))
            fi
          done
          echo "ROUND ${round}: progress ${done_count}/${#pids[@]} done, ${remaining} running"
          for idx in "${!meta[@]}"; do
            if [[ "${statuses[$idx]}" == "__pending__" ]]; then
              IFS='|' read -r run_id _b _w log _t <<<"${meta[$idx]}"
              local log_tail="<no log output yet>"
              if [[ -s "${log}" ]]; then
                log_tail="$(tail -n 1 "${log}" | tr -d '\r' | cut -c1-160)"
              fi
              echo "  ${run_id}: ${log_tail}"
            fi
          done
          last_report_ts="${now_ts}"
        fi
      fi
      sleep 1
    done
  fi

  for idx in "${!meta[@]}"; do
    IFS='|' read -r run_id branch wt log task_id <<<"${meta[$idx]}"
    local task_text="${meta_task_texts[$idx]}"
    local st="${statuses[$idx]}"
    local ahead=0
    local integrated=0

    # Keep task bookkeeping committed between agent merges to avoid dirty-tree merge failures.
    commit_supervisor_task_updates "supervisor: sync task bookkeeping before merge (${task_id})" || true

    if [[ "${st}" -eq 0 && "${DRY_RUN}" -eq 0 ]]; then
      if run_task_symbolic_validation "${task_text}" "${wt}" "${log}"; then
        echo "INFO: symbolic validation passed for task: ${task_text}" >>"${log}"
      else
        st=86
        echo "WARN: symbolic validation failed for task: ${task_text}" >>"${log}"
        echo "WARN: symbolic validation failed for ${branch}; task will not be checked off"
      fi
    fi

    if [[ "${DRY_RUN}" -eq 0 ]]; then
      ahead="$(git -C "${ROOT_DIR}" rev-list --count "HEAD..${branch}" 2>/dev/null || echo 0)"
    fi

    if ! push_and_cleanup "${branch}" "${wt}" "${log}" "${st}"; then
      echo "WARN: cleanup/merge step failed for ${branch}; lock status already finalized" >>"${log}"
      echo "WARN: cleanup/merge failed for ${branch} (see ${log})"
    fi
    integrated="${LAST_INTEGRATED}"

    if [[ "${st}" -eq 0 && ( "${DRY_RUN}" -eq 1 || "${ahead}" -gt 0 ) && "${integrated}" -eq 1 ]]; then
      if [[ "${DRY_RUN}" -eq 1 ]] || task_marked_checked_in_active_section "${task_text}"; then
        TOTAL_OK=$((TOTAL_OK + 1))
        SUMMARY_OK+=("${task_text}")
        mark_task_done "${task_id}"
      else
        TOTAL_FAIL=$((TOTAL_FAIL + 1))
        SUMMARY_FAIL+=("${task_text} (agent did not mark [x] in TASKS.md)")
        annotate_unchecked_task_needs_checkoff "${task_text}"
        release_task_lock "${task_id}"
      fi
    elif [[ "${st}" -eq 0 && "${ahead}" -gt 0 ]]; then
      TOTAL_FAIL=$((TOTAL_FAIL + 1))
      SUMMARY_FAIL+=("${task_text} (pending merge)")
      mark_task_pending_merge "${task_id}" "${branch}" "${wt}" "${log}"
      echo "WARN: task has commits but is not integrated into main; left as pending_merge: ${task_id}" >>"${log}"
    else
      TOTAL_FAIL=$((TOTAL_FAIL + 1))
      if [[ "${st}" -eq 86 ]]; then
        SUMMARY_FAIL+=("${task_text} (symbolic validation failed)")
      else
        SUMMARY_FAIL+=("${task_text}")
      fi
      release_task_lock "${task_id}"
      if [[ "${st}" -eq 0 && "${DRY_RUN}" -eq 0 && "${ahead}" -eq 0 ]]; then
        echo "WARN: agent exited 0 but made no commits on ${branch}; treating as failed" >>"${log}"
      fi
    fi

    TOTAL_AGENTS=$((TOTAL_AGENTS + 1))

    echo "AGENT ${run_id}: exit=${st} task='${task_text}' log=${log}"
  done

  commit_supervisor_task_updates "supervisor: sync round task bookkeeping (round ${round})" || true

  return 0
}

run_test_cmd() {
  local round="$1"
  local sup_log="${LOG_ROOT}/supervisor_round_${round}_$(timestamp).log"
  echo "ROUND ${round}: running test gate: ${TEST_CMD}"
  LAST_TEST_LOG="${sup_log}"

  if [[ "${DRY_RUN}" -eq 1 ]]; then
    echo "[dry-run] (cd ${ROOT_DIR} && ${TEST_CMD})"
    echo "ROUND ${round}: test=PASS(dry-run)"
    LAST_TEST_PASS="PASS(dry-run)"
    return 0
  fi

  if (cd "${ROOT_DIR}" && bash -lc "${TEST_CMD}") >"${sup_log}" 2>&1; then
    echo "ROUND ${round}: test=PASS log=${sup_log}"
    LAST_TEST_PASS="PASS"
    return 0
  else
    echo "ROUND ${round}: test=FAIL log=${sup_log}"
    LAST_TEST_PASS="FAIL"
    record_test_failure_todo "${round}" "${sup_log}"
    return 1
  fi
}

run_spawn_mode() {
  setup
  spawn_round 1 || true
  review_checked_tasks_with_validators 1 || true
  commit_supervisor_task_updates "supervisor: persist validator task updates (round 1)" || true
}

run_supervise_mode() {
  setup
  local round=1
  while :; do
    if [[ "${MAX_ROUNDS}" -gt 0 && "${round}" -gt "${MAX_ROUNDS}" ]]; then
      echo "Supervisor reached max rounds (${MAX_ROUNDS}); stopping."
      return 0
    fi

    if ! spawn_round "${round}"; then
      echo "Supervisor: stopping because no tasks were available."
      return 0
    fi

    review_checked_tasks_with_validators "${round}" || true
    commit_supervisor_task_updates "supervisor: persist validator task updates (round ${round})" || true

    if run_test_cmd "${round}"; then
      if [[ "${STOP_ON_PASS}" -eq 1 ]]; then
        echo "Supervisor: tests are passing; stopping."
        return 0
      fi
    fi

    round=$((round + 1))
    echo "Supervisor: sleeping ${SLEEP_SECS}s before next round."
    if [[ "${DRY_RUN}" -eq 1 ]]; then
      return 0
    fi
    sleep "${SLEEP_SECS}"
  done
}

parse_args "$@"
if [[ "${MODE}" == "spawn" ]]; then
  run_spawn_mode
else
  run_supervise_mode
fi
