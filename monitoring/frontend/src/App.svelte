<script>
  import { onDestroy, onMount } from "svelte";

  let snapshot = null;
  let status = "connecting";
  let selectedLog = null;
  let logLines = [];
  let pollTimer = null;
  let es = null;

  async function fetchSnapshot() {
    const res = await fetch("/api/snapshot");
    if (!res.ok) {
      throw new Error(`snapshot ${res.status}`);
    }
    snapshot = await res.json();
    status = "live";
  }

  async function fetchLog(name) {
    selectedLog = name;
    const res = await fetch(`/api/log/${encodeURIComponent(name)}?lines=220`);
    if (!res.ok) {
      logLines = [`unable to load log: ${name}`];
      return;
    }
    const data = await res.json();
    logLines = data.lines || [];
  }

  function startPolling() {
    if (pollTimer) return;
    pollTimer = setInterval(() => {
      fetchSnapshot().catch(() => {
        status = "poll-error";
      });
      if (selectedLog) {
        fetchLog(selectedLog).catch(() => {
          status = "poll-error";
        });
      }
    }, 2500);
  }

  function connectStream() {
    es = new EventSource("/api/stream");
    es.addEventListener("snapshot", (evt) => {
      snapshot = JSON.parse(evt.data);
      status = "live-stream";
      if (selectedLog) {
        fetchLog(selectedLog).catch(() => {
          status = "log-error";
        });
      }
    });
    es.onerror = () => {
      status = "stream-disconnected";
      if (es) {
        es.close();
        es = null;
      }
      startPolling();
    };
  }

  onMount(async () => {
    try {
      await fetchSnapshot();
    } catch {
      status = "initial-fetch-error";
    }
    connectStream();
  });

  onDestroy(() => {
    if (es) es.close();
    if (pollTimer) clearInterval(pollTimer);
  });

  $: taskDone = snapshot?.tasks?.done ?? 0;
  $: taskTodo = snapshot?.tasks?.todo ?? 0;
  $: lockCount = snapshot?.locks?.length ?? 0;
  $: agentCount = snapshot?.agent_logs?.length ?? 0;
</script>

<div class="container">
  <div class="top">
    <div class="title">VerifiedJS Supervisor Monitor</div>
    <div class="state">
      status: {status}
      {#if snapshot?.timestamp}
        | updated: {snapshot.timestamp}
      {/if}
    </div>
  </div>

  <div class="cards">
    <div class="card">
      <div class="label">TASKS DONE</div>
      <div class="value">{taskDone}</div>
    </div>
    <div class="card">
      <div class="label">TASKS TODO</div>
      <div class="value">{taskTodo}</div>
    </div>
    <div class="card">
      <div class="label">ACTIVE LOCKS</div>
      <div class="value">{lockCount}</div>
    </div>
    <div class="card">
      <div class="label">AGENT LOGS</div>
      <div class="value">{agentCount}</div>
    </div>
  </div>

  <div class="layout">
    <section class="panel">
      <h3>Recent Agent Logs</h3>
      <div class="list">
        {#if snapshot?.agent_logs?.length}
          {#each snapshot.agent_logs as log}
            <div
              class="row {selectedLog === log.name ? 'active' : ''}"
              on:click={() => fetchLog(log.name)}
            >
              <div>{log.name}</div>
              <div class="meta">{log.mtime} | {log.size} bytes</div>
              {#if log.last_line}
                <div class="meta">{log.last_line}</div>
              {/if}
            </div>
          {/each}
        {:else}
          <div class="row small">no agent logs found</div>
        {/if}
      </div>
    </section>

    <section class="panel">
      <h3>Live Log Tail {selectedLog ? `- ${selectedLog}` : ""}</h3>
      <pre class="mono">{logLines.length ? logLines.join("\n") : "select a log from the left panel"}</pre>
    </section>

    <section class="panel">
      <h3>Locks</h3>
      <div class="list">
        {#if snapshot?.locks?.length}
          {#each snapshot.locks as lock}
            <div class="row">
              <div>{lock.id}</div>
              {#if lock.meta?.task}
                <div class="meta">{lock.meta.task}</div>
              {/if}
              {#if lock.meta?.status}
                <div class="meta">status: {lock.meta.status}</div>
              {/if}
            </div>
          {/each}
        {:else}
          <div class="row small">no active locks</div>
        {/if}
      </div>
    </section>

    <section class="panel">
      <h3>Git + Supervisor Logs</h3>
      <div class="list">
        {#if snapshot?.git_status?.length}
          {#each snapshot.git_status as line}
            <div class="row small">{line}</div>
          {/each}
        {:else}
          <div class="row small">git status unavailable</div>
        {/if}
      </div>
      <div class="git">
        <h3>Recent Supervisor Logs</h3>
        <div class="list">
          {#if snapshot?.supervisor_logs?.length}
            {#each snapshot.supervisor_logs as log}
              <div class="row" on:click={() => fetchLog(log.name)}>
                <div>{log.name}</div>
                <div class="meta">{log.mtime}</div>
              </div>
            {/each}
          {:else}
            <div class="row small">no supervisor logs</div>
          {/if}
        </div>
      </div>
    </section>
  </div>
</div>
