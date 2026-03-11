<script>
  import { onDestroy, onMount } from "svelte";
  import hljs from "highlight.js/lib/core";
  import python from "highlight.js/lib/languages/python";

  hljs.registerLanguage("python", python);

  let snapshot = $state(null);
  let status = $state("connecting");
  let selectedTask = $state(null);
  let pollTimer = null;
  let es = null;

  // ── Agent process state ──
  let procState = $state("stopped"); // stopped | running | exited
  let procPid = $state(null);
  let procExitCode = $state(null);
  let termLines = $state([]);
  let termEl = $state(null);
  let logEs = null;
  let autoScroll = $state(true);
  const MAX_TERM_LINES = 3000;

  async function startAgents() {
    const res = await fetch("/api/agents/start", { method: "POST", headers: { "Content-Type": "application/json" }, body: "{}" });
    const data = await res.json();
    if (data.error) { termLines = [...termLines, { ts: Date.now() / 1000, text: `[monitor] Error: ${data.error}` }]; return; }
    procState = "running";
    procPid = data.pid;
    procExitCode = null;
    termLines = [{ ts: Date.now() / 1000, text: `[monitor] Started agent process (PID ${data.pid})` }];
    connectLogStream();
  }

  async function stopAgents() {
    termLines = [...termLines, { ts: Date.now() / 1000, text: "[monitor] Sending SIGINT..." }];
    const res = await fetch("/api/agents/stop", { method: "POST" });
    const data = await res.json();
    procState = data.state === "stopped" || data.state === "not_running" ? "stopped" : "exited";
    procExitCode = data.exit_code ?? null;
    termLines = [...termLines, { ts: Date.now() / 1000, text: `[monitor] Process stopped (exit=${data.exit_code ?? "?"})` }];
  }

  function connectLogStream() {
    if (logEs) { logEs.close(); logEs = null; }
    logEs = new EventSource("/api/agents/log/stream");
    logEs.addEventListener("line", (evt) => {
      const entry = JSON.parse(evt.data);
      termLines = [...termLines.slice(-MAX_TERM_LINES), entry];
      if (autoScroll && termEl) {
        requestAnimationFrame(() => { termEl.scrollTop = termEl.scrollHeight; });
      }
    });
    logEs.addEventListener("exit", (evt) => {
      const data = JSON.parse(evt.data);
      procState = "exited";
      procExitCode = data.exit_code;
      termLines = [...termLines, { ts: Date.now() / 1000, text: `[monitor] Process exited (code=${data.exit_code ?? "?"})` }];
      if (logEs) { logEs.close(); logEs = null; }
    });
    logEs.onerror = () => {
      if (logEs) { logEs.close(); logEs = null; }
    };
  }

  // Sync process status from snapshot
  function syncProcStatus(snap) {
    if (!snap?.agent_process) return;
    const ap = snap.agent_process;
    if (ap.state === "running" && procState !== "running") {
      procState = "running";
      procPid = ap.pid;
      // Reconnect log stream if we missed the start (e.g. page reload)
      if (!logEs) {
        // Fetch existing log first
        fetch("/api/agents/log").then(r => r.json()).then(lines => {
          termLines = lines;
          connectLogStream();
          if (autoScroll && termEl) {
            requestAnimationFrame(() => { termEl.scrollTop = termEl.scrollHeight; });
          }
        }).catch(() => {});
      }
    } else if (ap.state === "exited" && procState === "running") {
      procState = "exited";
      procExitCode = ap.exit_code;
    } else if (ap.state === "stopped" && procState !== "stopped" && procState !== "exited") {
      procState = "stopped";
    }
  }

  // Highlight full source and split into per-line HTML
  function highlightLines(lines) {
    if (!lines || lines.length === 0) return [];
    const fullSource = lines.map(l => l.text).join("\n");
    const highlighted = hljs.highlight(fullSource, { language: "python" }).value;
    const htmlLines = [];
    let openSpans = [];
    for (const raw of highlighted.split("\n")) {
      let prefix = openSpans.join("");
      let lineHtml = prefix + raw;
      const opens = raw.match(/<span[^>]*>/g) || [];
      const closes = raw.match(/<\/span>/g) || [];
      for (const o of opens) openSpans.push(o);
      for (let i = 0; i < closes.length; i++) openSpans.pop();
      let suffix = "</span>".repeat(openSpans.length);
      htmlLines.push(lineHtml + suffix);
    }
    return htmlLines;
  }

  function cursorsForLine(lineNum, phases, agentPositions) {
    if (!phases || !agentPositions) return [];
    const cursors = [];
    for (const phase of phases) {
      if (phase.line > 0 && lineNum >= phase.line && lineNum < phase.line + 3) {
        for (const [agent, phaseId] of Object.entries(agentPositions)) {
          if (phaseId === phase.id) cursors.push(agent);
        }
      }
    }
    return cursors;
  }

  function phaseLineRange(phaseId, phases) {
    if (!phases) return [0, 0];
    const idx = phases.findIndex(p => p.id === phaseId);
    if (idx === -1) return [0, 0];
    const start = phases[idx].line;
    const end = idx + 1 < phases.length ? phases[idx + 1].line - 1 : start + 30;
    return [start, end];
  }

  async function fetchSnapshot() {
    const res = await fetch("/api/snapshot");
    if (!res.ok) throw new Error(`snapshot ${res.status}`);
    snapshot = await res.json();
    status = "live";
    syncProcStatus(snapshot);
  }

  function startPolling() {
    if (pollTimer) return;
    pollTimer = setInterval(() => {
      fetchSnapshot().catch(() => { status = "poll-error"; });
    }, 3000);
  }

  function connectStream() {
    es = new EventSource("/api/stream");
    es.addEventListener("snapshot", (evt) => {
      snapshot = JSON.parse(evt.data);
      status = "live";
      syncProcStatus(snapshot);
    });
    es.onerror = () => {
      status = "disconnected";
      if (es) { es.close(); es = null; }
      startPolling();
    };
  }

  onMount(async () => {
    try { await fetchSnapshot(); } catch { status = "error"; }
    connectStream();
  });

  onDestroy(() => {
    if (es) es.close();
    if (logEs) logEs.close();
    if (pollTimer) clearInterval(pollTimer);
  });

  // Derived state
  let tasks = $derived(snapshot?.tasks ?? []);
  let stats = $derived(snapshot?.task_stats ?? { total: 0, by_status: {}, by_type: {}, by_owner: {} });
  let checkpoints = $derived(snapshot?.checkpoints ?? []);
  let choreo = $derived(snapshot?.choreography ?? { lines: [], phases: [] });
  let activePhase = $derived(snapshot?.active_phase ?? "plan");
  let tasksMd = $derived(snapshot?.tasks_md ?? { sections: [], total: 0, done: 0 });
  let git = $derived(snapshot?.git ?? { status: [], recent_commits: [] });
  let agentPositions = $derived(snapshot?.agent_positions ?? {});
  let selectedTaskData = $derived(selectedTask ? tasks.find(t => t.id === selectedTask) : null);
  let highlightedLines = $derived(highlightLines(choreo?.lines));

  function statusClass(s) {
    if (s === "live" || s === "live-stream") return "live";
    if (s.includes("error") || s === "disconnected") return "error";
    return "connecting";
  }
  function shortId(id) { return id.length <= 20 ? id : id.slice(0, 18) + "..."; }
  function truncate(s, n = 80) { return !s ? "" : s.length > n ? s.slice(0, n) + "..." : s; }
  function scrollToPhase(phaseId) {
    const phase = choreo.phases.find(p => p.id === phaseId);
    if (phase?.line) {
      const el = document.getElementById(`line-${phase.line}`);
      if (el) el.scrollIntoView({ behavior: "smooth", block: "center" });
    }
  }
  function fmtTs(ts) {
    if (!ts) return "";
    const d = new Date(ts * 1000);
    return d.toLocaleTimeString("en-GB", { hour12: false });
  }
</script>

<div class="app">
  <div class="header">
    <div class="header-left">
      <div class="header-title">VerifiedJS Agent Monitor</div>
      <div class="header-meta">
        <span class="status-dot {statusClass(status)}"></span>
        {status}
        {#if snapshot?.timestamp}
          &middot; {snapshot.timestamp.split("T")[1]?.split(".")[0] ?? ""}
        {/if}
      </div>
    </div>
    <div class="header-controls">
      {#if procState === "running"}
        <span class="proc-badge running">PID {procPid}</span>
        <button class="btn btn-stop" onclick={stopAgents}>Stop Agents</button>
      {:else}
        {#if procState === "exited"}
          <span class="proc-badge exited">exited ({procExitCode ?? "?"})</span>
        {/if}
        <button class="btn btn-start" onclick={startAgents}>Start Agents</button>
      {/if}
    </div>
  </div>

  <!-- Stats row -->
  <div class="stats-row">
    <div class="stat">
      <div class="stat-label">Queue Tasks</div>
      <div class="stat-value">{stats.total}</div>
    </div>
    <div class="stat">
      <div class="stat-label">Done</div>
      <div class="stat-value" style="color: #16a34a">{stats.by_status?.done ?? 0}</div>
    </div>
    <div class="stat">
      <div class="stat-label">Claimed</div>
      <div class="stat-value" style="color: #d97706">{stats.by_status?.claimed ?? 0}</div>
    </div>
    <div class="stat">
      <div class="stat-label">Pending</div>
      <div class="stat-value" style="color: #64748b">{stats.by_status?.pending ?? 0}</div>
    </div>
    <div class="stat">
      <div class="stat-label">Active Agents</div>
      <div class="stat-value">{checkpoints.length}</div>
    </div>
    <div class="stat">
      <div class="stat-label">Active Phase</div>
      <div class="stat-value sm">
        <button onclick={() => scrollToPhase(activePhase)} style="background:none;border:none;color:#3b82f6;cursor:pointer;font:inherit;font-weight:700;padding:0;">
          {activePhase}
        </button>
      </div>
    </div>
    {#if tasksMd.total > 0}
      <div class="stat">
        <div class="stat-label">TASKS.md</div>
        <div class="stat-value">{tasksMd.done}/{tasksMd.total}</div>
      </div>
    {/if}
  </div>

  <!-- Terminal -->
  <div class="panel term-panel" style="margin-bottom: 10px;">
    <div class="panel-header">
      Process Output
      <span style="font-weight:400;text-transform:none;display:flex;align-items:center;gap:8px;">
        <span class="proc-indicator {procState}"></span>
        {procState}{procState === "running" ? ` (PID ${procPid})` : ""}
        {#if procState === "exited"} &middot; exit {procExitCode ?? "?"}{/if}
        &middot; {termLines.length} lines
        <label style="font-size:10px;display:flex;align-items:center;gap:3px;cursor:pointer;">
          <input type="checkbox" bind:checked={autoScroll} style="margin:0;" /> auto-scroll
        </label>
        <button class="btn-sm" onclick={() => { termLines = []; }}>Clear</button>
      </span>
    </div>
    <div class="term-body" bind:this={termEl}>
      {#each termLines as line}
        <div class="term-line">
          <span class="term-ts">{fmtTs(line.ts)}</span>
          <span class="term-text">{line.text}</span>
        </div>
      {/each}
      {#if termLines.length === 0}
        <div class="empty" style="padding:20px;">
          {procState === "stopped" ? 'Click "Start Agents" to run the choreography' : "Waiting for output..."}
        </div>
      {/if}
    </div>
  </div>

  <!-- Choreography source viewer -->
  {#if choreo.lines.length > 0}
    <div class="panel code-panel" style="margin-bottom: 10px;">
      <div class="panel-header">
        Choreography &mdash; verified_compiler_development_loop
        <span style="font-weight:400;text-transform:none;">
          Lines {choreo.func_start}&ndash;{choreo.func_end}
        </span>
      </div>
      <div class="code-scroll panel-body tall">
        {#each choreo.lines as line, idx}
          {@const isPhaseStart = choreo.phases.some(p => p.line === line.num)}
          {@const isInActivePhase = (() => {
            const [s, e] = phaseLineRange(activePhase, choreo.phases);
            return line.num >= s && line.num <= e;
          })()}
          {@const lineCursors = cursorsForLine(line.num, choreo.phases, agentPositions)}
          <div
            id="line-{line.num}"
            class="code-line"
            class:phase-active={isPhaseStart && isInActivePhase}
            class:phase-highlight={!isPhaseStart && isInActivePhase}
          >
            <span class="line-num">{line.num}</span>
            <span class="line-text">{@html highlightedLines[idx] ?? line.text}</span>
            {#if lineCursors.length > 0}
              <span class="line-cursors">
                {#each lineCursors as agent}
                  <span class="agent-cursor {agent}">{agent}</span>
                {/each}
              </span>
            {/if}
          </div>
        {/each}
      </div>
    </div>
  {/if}

  <div class="main-grid">
    <!-- Task Queue -->
    <div class="panel">
      <div class="panel-header">
        Task Queue
        <span style="font-weight:400">{tasks.length}</span>
      </div>
      <div class="panel-body">
        {#if tasks.length === 0}
          <div class="empty">No tasks in queue</div>
        {:else}
          {#each tasks as t}
            <div
              class="trow"
              class:selected={selectedTask === t.id}
              onclick={() => selectedTask = selectedTask === t.id ? null : t.id}
              role="button"
              tabindex="0"
              onkeydown={(e) => e.key === 'Enter' && (selectedTask = selectedTask === t.id ? null : t.id)}
            >
              <span class="trow-id">{shortId(t.id)}</span>
              <span class="badge type">{t.type.replace("scatter-", "")}</span>
              <span class="badge {t.status}">{t.status}</span>
              {#if t.owner}
                <span class="badge owner">{t.owner}</span>
              {/if}
              <span class="trow-detail">
                {#if t.details?.context_task_id}
                  {t.details.context_task_id}
                {:else if t.details?.planned_tasks}
                  {t.details.planned_tasks.length} tasks planned
                {:else if t.payload?.item_index !== undefined}
                  item #{t.payload.item_index}
                {/if}
              </span>
            </div>
          {/each}
        {/if}
      </div>
    </div>

    <!-- Task Detail -->
    <div class="panel">
      <div class="panel-header">Task Detail</div>
      <div class="panel-body">
        {#if selectedTaskData}
          <div class="detail-pane">
            <div class="detail-section">
              <div class="detail-kv"><span class="k">ID</span><span>{selectedTaskData.id}</span></div>
              <div class="detail-kv"><span class="k">Type</span><span class="badge type">{selectedTaskData.type}</span></div>
              <div class="detail-kv"><span class="k">Status</span><span class="badge {selectedTaskData.status}">{selectedTaskData.status}</span></div>
              <div class="detail-kv"><span class="k">Owner</span><span>{selectedTaskData.owner || "\u2014"}</span></div>
            </div>

            {#if selectedTaskData.details?.planned_tasks}
              <div class="detail-section">
                <h4>Planned Tasks ({selectedTaskData.details.planned_tasks.length})</h4>
                {#each selectedTaskData.details.planned_tasks as pt}
                  <div style="padding: 3px 0; border-bottom: 1px solid #f1f3f5;">
                    <strong>{pt.task_id}</strong>
                    <span class="badge type" style="margin-left:4px">{pt.task_type}</span>
                    <div style="font-size:11px;color:#64748b;margin-top:2px;">{truncate(pt.description, 120)}</div>
                    <div style="font-size:10px;color:#94a3b8;">{pt.target_file} &middot; {pt.ecma_spec_section}</div>
                  </div>
                {/each}
              </div>
              {#if selectedTaskData.details.rationale}
                <div class="detail-section">
                  <h4>Rationale</h4>
                  <pre>{selectedTaskData.details.rationale}</pre>
                </div>
              {/if}
            {/if}

            {#if selectedTaskData.details?.context_task_id}
              <div class="detail-section">
                <h4>Context for: {selectedTaskData.details.context_task_id}</h4>
                {#if selectedTaskData.details.context_files}
                  <div style="font-size:11px;">
                    Files: {selectedTaskData.details.context_files.join(", ")}
                  </div>
                {/if}
                {#if selectedTaskData.details.existing_sorrys?.length}
                  <div style="font-size:11px;margin-top:3px;">
                    Sorrys: {selectedTaskData.details.existing_sorrys.join(", ")}
                  </div>
                {/if}
              </div>
              {#if selectedTaskData.details.guidance}
                <div class="detail-section">
                  <h4>Guidance</h4>
                  <pre>{selectedTaskData.details.guidance}</pre>
                </div>
              {/if}
              {#if selectedTaskData.details.proof_blockers}
                <div class="detail-section">
                  <h4>Proof Blockers</h4>
                  <pre>{selectedTaskData.details.proof_blockers}</pre>
                </div>
              {/if}
            {/if}

            {#if selectedTaskData.details?.verdict}
              <div class="detail-section">
                <div class="detail-kv"><span class="k">Verdict</span><span class="badge {selectedTaskData.details.verdict === 'ACCEPT' ? 'done' : selectedTaskData.details.verdict === 'REVISE' ? 'claimed' : 'error'}">{selectedTaskData.details.verdict}</span></div>
                {#if selectedTaskData.details.feedback}
                  <pre style="margin-top:4px">{selectedTaskData.details.feedback}</pre>
                {/if}
              </div>
            {/if}

            {#if !selectedTaskData.details || Object.keys(selectedTaskData.details).length === 0}
              <div class="detail-section">
                <h4>Payload</h4>
                <pre>{JSON.stringify(selectedTaskData.payload, null, 2)}</pre>
              </div>
              {#if selectedTaskData.result}
                <div class="detail-section">
                  <h4>Result</h4>
                  <pre>{typeof selectedTaskData.result === "string" ? selectedTaskData.result : JSON.stringify(selectedTaskData.result, null, 2).slice(0, 2000)}</pre>
                </div>
              {/if}
            {/if}
          </div>
        {:else}
          <div class="empty">Click a task to view details</div>
        {/if}
      </div>
    </div>

    <!-- Agent Checkpoints -->
    <div class="panel">
      <div class="panel-header">
        Agent Checkpoints
        <span style="font-weight:400">{checkpoints.length}</span>
      </div>
      <div class="panel-body">
        {#if checkpoints.length === 0}
          <div class="empty">No agent checkpoints</div>
        {:else}
          {#each checkpoints as cp}
            <div class="agent-card">
              <div class="agent-dot" class:active={cp.handoff || cp.history_len > 0} class:idle={!cp.handoff && cp.history_len === 0}></div>
              <span class="agent-name">{cp.agent_id}</span>
              <span class="agent-handoff" title={cp.handoff}>{truncate(cp.handoff, 60) || "idle"}</span>
              <span class="agent-msgs">{cp.history_len} msgs</span>
            </div>
          {/each}
        {/if}
      </div>
    </div>

    <!-- Status sidebar -->
    <div class="panel">
      <div class="panel-header">Status</div>
      <div class="panel-body short">
        <div style="padding: 8px 10px;">
          <div style="font-size:11px;font-weight:600;color:#475569;margin-bottom:4px;">By Status</div>
          {#each Object.entries(stats.by_status) as [s, count]}
            <div style="display:flex;align-items:center;gap:6px;padding:2px 0;">
              <span class="badge {s}" style="min-width:55px;text-align:center">{s}</span>
              <span style="font-size:12px;font-weight:600">{count}</span>
            </div>
          {/each}
        </div>
        <div style="padding: 4px 10px 8px;">
          <div style="font-size:11px;font-weight:600;color:#475569;margin-bottom:4px;">By Owner</div>
          {#each Object.entries(stats.by_owner) as [owner, count]}
            <div style="display:flex;align-items:center;gap:6px;padding:2px 0;">
              <span class="badge owner" style="min-width:120px">{owner}</span>
              <span style="font-size:12px;font-weight:600">{count}</span>
            </div>
          {/each}
        </div>
        {#if git.recent_commits.length > 0}
          <div style="padding: 4px 10px 8px; border-top: 1px solid #e2e5ea;">
            <div style="font-size:11px;font-weight:600;color:#475569;margin-bottom:4px;">Recent Commits</div>
            {#each git.recent_commits.slice(0, 5) as c}
              <div style="font-size:11px;padding:1px 0;">
                <span style="color:#3b82f6;font-family:monospace">{c.hash}</span>
                <span style="color:#64748b">{c.message}</span>
              </div>
            {/each}
          </div>
        {/if}
      </div>
    </div>

    <!-- TASKS.md progress -->
    {#if tasksMd.sections.length > 0}
      <div class="panel full-width">
        <div class="panel-header">
          Project Progress (TASKS.md)
          <span style="font-weight:400">{tasksMd.done}/{tasksMd.total}</span>
        </div>
        <div class="panel-body short">
          {#each tasksMd.sections as sec}
            <div class="progress-row">
              <span class="progress-label">{sec.section}</span>
              <div class="progress-bar-bg">
                <div class="progress-bar-fill" style="width: {sec.total ? (sec.done / sec.total) * 100 : 0}%"></div>
              </div>
              <span class="progress-count">{sec.done}/{sec.total}</span>
            </div>
          {/each}
        </div>
      </div>
    {/if}
  </div>
</div>
