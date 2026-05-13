import { useCallback, useEffect, useMemo, useState } from "react";
import { useNavigate } from "react-router-dom";
import { api } from "../api";
import type {
  EvalEnvironment,
  EvalRunIndexEntry,
  EvalRunManifest,
  EvalStatus,
  LaunchEvalRunRequest,
} from "../types";

type ActionName = "refresh" | "report" | "launch" | `teardown-${number}`;

const DEFAULT_CONFIG =
  "/Users/cvick-admin/Documents/research/yardbird/garden/benchmark_config.yaml";

function statusClass(status: EvalStatus) {
  return `status-pill ${status.toLowerCase()}`;
}

function formatDate(value: string | null | undefined) {
  if (!value) return "-";
  return new Date(value).toLocaleString();
}

function splitMatrices(value: string) {
  return value
    .split(/[\n,]+/)
    .map((item) => item.trim())
    .filter(Boolean);
}

export default function EvalRunsPage() {
  const navigate = useNavigate();
  const [runs, setRuns] = useState<EvalRunIndexEntry[]>([]);
  const [selectedRunId, setSelectedRunId] = useState<string | null>(null);
  const [manifest, setManifest] = useState<EvalRunManifest | null>(null);
  const [loadingRuns, setLoadingRuns] = useState(true);
  const [loadingManifest, setLoadingManifest] = useState(false);
  const [activeAction, setActiveAction] = useState<ActionName | null>(null);
  const [message, setMessage] = useState<string | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [env, setEnv] = useState<EvalEnvironment>("lab");
  const [name, setName] = useState("");
  const [matrices, setMatrices] = useState("quick");
  const [config, setConfig] = useState(DEFAULT_CONFIG);
  const [workerTemplate, setWorkerTemplate] = useState("");
  const [workerSshKey, setWorkerSshKey] = useState("");
  const [r2Prefix, setR2Prefix] = useState("main-eval");
  const [keepVms, setKeepVms] = useState(false);
  const [proxmoxInsecure, setProxmoxInsecure] = useState(true);

  const selectedIndexEntry = useMemo(
    () => runs.find((run) => run.run_id === selectedRunId) ?? null,
    [runs, selectedRunId],
  );

  const loadRuns = useCallback(async (nextSelectedRunId?: string) => {
    setLoadingRuns(true);
    const data = await api.evalRuns();
    setRuns(data.runs);
    setSelectedRunId(
      (current) => nextSelectedRunId ?? current ?? data.runs[0]?.run_id ?? null,
    );
    setLoadingRuns(false);
  }, []);

  const loadManifest = async (runId: string) => {
    setLoadingManifest(true);
    const data = await api.evalRun(runId);
    setManifest(data);
    setLoadingManifest(false);
  };

  useEffect(() => {
    loadRuns().catch((err: Error) => {
      setError(err.message);
      setLoadingRuns(false);
    });
  }, [loadRuns]);

  useEffect(() => {
    if (!selectedRunId) {
      setManifest(null);
      return;
    }
    loadManifest(selectedRunId).catch((err: Error) => {
      setError(err.message);
      setLoadingManifest(false);
    });
  }, [selectedRunId]);

  const runAction = async (
    action: ActionName,
    work: () => Promise<{ manifest?: EvalRunManifest }>,
    successMessage: string,
  ) => {
    setActiveAction(action);
    setMessage(null);
    setError(null);
    try {
      const result = await work();
      if (result.manifest) setManifest(result.manifest);
      await loadRuns(result.manifest?.run_id);
      setMessage(successMessage);
    } catch (err) {
      setError(err instanceof Error ? err.message : String(err));
    } finally {
      setActiveAction(null);
    }
  };

  const launchRun = async () => {
    const benchmarkTypes = splitMatrices(matrices);
    if (benchmarkTypes.length === 0) {
      setError("Add at least one benchmark matrix");
      return;
    }
    const request: LaunchEvalRunRequest = {
      env,
      benchmarkTypes,
      name: name.trim() || undefined,
      config: config.trim() || undefined,
      lab:
        env === "lab"
          ? {
              proxmoxInsecure,
              workerTemplate: workerTemplate.trim() || undefined,
              workerSshKey: workerSshKey.trim() || undefined,
              r2Prefix: r2Prefix.trim() || undefined,
              keepVms,
            }
          : undefined,
    };
    await runAction(
      "launch",
      async () => {
        const result = await api.launchEvalRun(request);
        const launchedId = result.index?.runs[0]?.run_id;
        if (!launchedId) return {};
        return { manifest: await api.evalRun(launchedId) };
      },
      "Run launched",
    );
  };

  const subruns = manifest?.subruns ?? [];

  return (
    <div className="eval-page">
      <div className="pane eval-sidebar">
        <div className="detail-header">
          <button className="back-btn" onClick={() => navigate("/")}>
            Benchmarks
          </button>
          <h2>Eval Runs</h2>
        </div>

        <div className="launch-panel">
          <h3>New Run</h3>
          <div className="field-row">
            <label>Env</label>
            <select value={env} onChange={(event) => setEnv(event.target.value as EvalEnvironment)}>
              <option value="lab">lab</option>
              <option value="local">local</option>
              <option value="aws">aws</option>
            </select>
          </div>
          <div className="field-row">
            <label>Name</label>
            <input value={name} onChange={(event) => setName(event.target.value)} />
          </div>
          <div className="field-row">
            <label>Matrices</label>
            <textarea
              rows={3}
              value={matrices}
              onChange={(event) => setMatrices(event.target.value)}
            />
          </div>
          <div className="field-row">
            <label>Config</label>
            <input value={config} onChange={(event) => setConfig(event.target.value)} />
          </div>
          {env === "lab" && (
            <>
              <div className="field-row">
                <label>Template</label>
                <input
                  value={workerTemplate}
                  onChange={(event) => setWorkerTemplate(event.target.value)}
                  placeholder="from .env"
                />
              </div>
              <div className="field-row">
                <label>SSH key</label>
                <input
                  value={workerSshKey}
                  onChange={(event) => setWorkerSshKey(event.target.value)}
                  placeholder="from .env"
                />
              </div>
              <div className="field-row">
                <label>R2 prefix</label>
                <input value={r2Prefix} onChange={(event) => setR2Prefix(event.target.value)} />
              </div>
              <label className="check-row">
                <input
                  type="checkbox"
                  checked={proxmoxInsecure}
                  onChange={(event) => setProxmoxInsecure(event.target.checked)}
                />
                Proxmox insecure TLS
              </label>
              <label className="check-row">
                <input
                  type="checkbox"
                  checked={keepVms}
                  onChange={(event) => setKeepVms(event.target.checked)}
                />
                Keep worker VMs
              </label>
            </>
          )}
          <button
            className="primary-btn"
            disabled={activeAction === "launch"}
            onClick={launchRun}
          >
            {activeAction === "launch" ? "Launching..." : "Launch"}
          </button>
        </div>

        <div className="run-count">{runs.length} eval runs</div>
        {loadingRuns ? (
          <div>Loading...</div>
        ) : (
          <div className="benchmark-list">
            {runs.map((run) => (
              <div
                key={run.run_id}
                className={`benchmark-item ${run.run_id === selectedRunId ? "active" : ""}`}
                onClick={() => setSelectedRunId(run.run_id)}
              >
                <div className="benchmark-name" title={run.run_id}>
                  {run.name ?? run.run_id}
                </div>
                <div className="benchmark-meta">
                  <span className={statusClass(run.status)}>{run.status}</span>
                  <span>{run.env}</span>
                  <span>{run.benchmark_types.join(", ")}</span>
                </div>
              </div>
            ))}
          </div>
        )}
      </div>

      <div className="pane eval-detail">
        {message && <div className="notice success">{message}</div>}
        {error && <div className="notice error">{error}</div>}
        {!selectedRunId && <div className="empty">No eval runs yet</div>}
        {selectedRunId && (loadingManifest || !manifest) && <div>Loading run...</div>}
        {manifest && !loadingManifest && (
          <>
            <div className="detail-header eval-detail-header">
              <div>
                <h2>{manifest.name}</h2>
                <div className="muted mono">{manifest.run_id}</div>
              </div>
              <span className={statusClass(manifest.status)}>{manifest.status}</span>
              <button
                className="back-btn"
                disabled={activeAction === "refresh"}
                onClick={() =>
                  runAction(
                    "refresh",
                    () => api.refreshEvalRun(manifest.run_id),
                    "Status refreshed",
                  )
                }
              >
                {activeAction === "refresh" ? "Refreshing..." : "Refresh"}
              </button>
              <button
                className="primary-btn"
                disabled={activeAction === "report" || manifest.status !== "COMPLETED"}
                onClick={() =>
                  runAction(
                    "report",
                    () => api.downloadReport(manifest.run_id),
                    "Artifacts downloaded and report generated",
                  )
                }
              >
                {activeAction === "report" ? "Working..." : "Download + Report"}
              </button>
            </div>

            <div className="summary-cards">
              <div className="card">
                <div className="card-label">Env</div>
                <div className="card-value">{manifest.env}</div>
              </div>
              <div className="card">
                <div className="card-label">Progress</div>
                <div className="card-value">
                  {manifest.progress.completed}/{manifest.progress.total}
                </div>
              </div>
              <div className="card">
                <div className="card-label">Failed</div>
                <div className="card-value">{manifest.progress.failed}</div>
              </div>
              <div className="card">
                <div className="card-label">Started</div>
                <div className="card-value compact">{formatDate(manifest.started_at)}</div>
              </div>
              <div className="card">
                <div className="card-label">Updated</div>
                <div className="card-value compact">{formatDate(manifest.updated_at)}</div>
              </div>
            </div>

            <div className="manifest-path mono">{manifest.manifest_path}</div>
            {selectedIndexEntry && (
              <div className="muted">
                Matrices: {selectedIndexEntry.benchmark_types.join(", ")}
              </div>
            )}

            <h3>Subruns</h3>
            <div className="subrun-list">
              {subruns.map((subrun, index) => {
                const terminal =
                  subrun.status === "COMPLETED" || subrun.status === "FAILED";
                const destroyed = Boolean(subrun.worker_destroyed_at);
                const actionName: ActionName = `teardown-${index}`;
                return (
                  <div className="subrun-card" key={`${subrun.benchmark_type}-${index}`}>
                    <div className="subrun-header">
                      <div>
                        <div className="subrun-title">{subrun.benchmark_type}</div>
                        <div className="muted">
                          {subrun.worker_name ?? "worker"} on{" "}
                          {subrun.worker_node ?? "-"}
                        </div>
                      </div>
                      <span className={statusClass(subrun.status)}>{subrun.status}</span>
                    </div>
                    <div className="subrun-grid">
                      <div>
                        <span>VMID</span>
                        <strong>{subrun.worker_vmid ?? "-"}</strong>
                      </div>
                      <div>
                        <span>IP</span>
                        <strong>{subrun.worker_ip ?? "-"}</strong>
                      </div>
                      <div>
                        <span>VM state</span>
                        <strong>{subrun.last_observed_vm_state ?? "-"}</strong>
                      </div>
                      <div>
                        <span>Completed</span>
                        <strong>{formatDate(subrun.completed_at)}</strong>
                      </div>
                      <div>
                        <span>Cleanup</span>
                        <strong>
                          {destroyed
                            ? "destroyed"
                            : subrun.cleanup_pending
                              ? "pending"
                              : "available"}
                        </strong>
                      </div>
                      <div>
                        <span>R2</span>
                        <strong title={subrun.r2_results_key}>{subrun.r2_prefix ?? "-"}</strong>
                      </div>
                    </div>
                    {subrun.error && <div className="notice error">{subrun.error}</div>}
                    {subrun.cleanup_error && (
                      <div className="notice error">{subrun.cleanup_error}</div>
                    )}
                    {manifest.env === "lab" && (
                      <button
                        className="danger-btn"
                        disabled={!terminal || destroyed || activeAction === actionName}
                        onClick={() =>
                          runAction(
                            actionName,
                            () => api.teardownSubrun(manifest.run_id, index),
                            `Subrun ${subrun.benchmark_type} torn down`,
                          )
                        }
                      >
                        {destroyed
                          ? "Torn down"
                          : activeAction === actionName
                            ? "Tearing down..."
                            : "Teardown VM"}
                      </button>
                    )}
                  </div>
                );
              })}
            </div>
          </>
        )}
      </div>
    </div>
  );
}
