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

SCRIPT_START_TS="$(date +%s)"
SUMMARY_PRINTED=0
TOTAL_ROUNDS=0
TOTAL_AGENTS=0
TOTAL_OK=0
TOTAL_FAIL=0
LAST_TEST_PASS="N/A"
declare -a SUMMARY_OK
declare -a SUMMARY_FAIL
declare -a ROUND_TASK_IDS
declare -a ROUND_TASK_TEXTS
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

release_task_lock() {
  local task_id="$1"
  local lock_path="${LOCK_DIR}/${task_id}"
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    return 0
  fi
  rm -rf "${lock_path}"
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
  prompt+="Implement the task, run ./tests/run_tests.sh --fast, commit your changes, and exit."$'\n'

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

  if [[ "${PUSH_AFTER_RUN}" -eq 0 && "${MERGE_LOCAL}" -eq 1 && "${st}" -eq 0 && "${DRY_RUN}" -eq 0 ]]; then
    local ahead
    ahead="$(git -C "${ROOT_DIR}" rev-list --count "HEAD..${branch}" 2>/dev/null || echo 0)"
    if [[ "${ahead}" -gt 0 ]]; then
      if git -C "${ROOT_DIR}" diff --quiet && git -C "${ROOT_DIR}" diff --cached --quiet; then
        if git -C "${ROOT_DIR}" merge --no-ff "${branch}" -m "Merge ${branch}"; then
          merged=1
          echo "INFO: merged ${branch} into $(git -C "${ROOT_DIR}" branch --show-current)" >>"${log}"
        else
          echo "WARN: merge failed for ${branch}; leaving branch/worktree for manual resolve" >>"${log}"
          echo "WARN: merge failed for ${branch}; keeping local state"
          return 0
        fi
      else
        echo "WARN: root tree dirty; skipping auto-merge for ${branch}; keeping branch/worktree for manual merge" >>"${log}"
        echo "WARN: root tree dirty; retained ${branch} at ${wt} for manual merge"
        return 0
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

collect_assignments() {
  local needed="$1"
  ROUND_TASK_IDS=()
  ROUND_TASK_TEXTS=()

  local got=0
  while IFS='|' read -r line_no task_text; do
    local task_id
    task_id="$(slug_for_task "${line_no}" "${task_text}")"
    if claim_task "${task_id}" "${task_text}"; then
      ROUND_TASK_IDS+=("${task_id}")
      ROUND_TASK_TEXTS+=("${task_text}")
      got=$((got + 1))
      if [[ "${got}" -ge "${needed}" ]]; then
        break
      fi
    fi
  done < <(unchecked_tasks)
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
    if [[ "${DRY_RUN}" -eq 0 ]]; then
      ahead="$(git -C "${ROOT_DIR}" rev-list --count "HEAD..${branch}" 2>/dev/null || echo 0)"
    fi

    if [[ "${st}" -eq 0 && ( "${DRY_RUN}" -eq 1 || "${ahead}" -gt 0 ) ]]; then
      TOTAL_OK=$((TOTAL_OK + 1))
      SUMMARY_OK+=("${task_text}")
      mark_task_done "${task_id}"
      mark_task_done_in_tasks "${task_id}" "${task_text}"
    else
      TOTAL_FAIL=$((TOTAL_FAIL + 1))
      SUMMARY_FAIL+=("${task_text}")
      release_task_lock "${task_id}"
      if [[ "${st}" -eq 0 && "${DRY_RUN}" -eq 0 && "${ahead}" -eq 0 ]]; then
        echo "WARN: agent exited 0 but made no commits on ${branch}; treating as failed" >>"${log}"
      fi
    fi

    if ! push_and_cleanup "${branch}" "${wt}" "${log}" "${st}"; then
      echo "WARN: cleanup/merge step failed for ${branch}; lock status already finalized" >>"${log}"
      echo "WARN: cleanup/merge failed for ${branch} (see ${log})"
    fi

    TOTAL_AGENTS=$((TOTAL_AGENTS + 1))

    echo "AGENT ${run_id}: exit=${st} task='${task_text}' log=${log}"
  done

  return 0
}

run_test_cmd() {
  local round="$1"
  local sup_log="${LOG_ROOT}/supervisor_round_${round}_$(timestamp).log"
  echo "ROUND ${round}: running test gate: ${TEST_CMD}"

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
    return 1
  fi
}

run_spawn_mode() {
  setup
  spawn_round 1 || true
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
