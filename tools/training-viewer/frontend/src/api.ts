import type {
  BenchmarkSummary,
  RunSummary,
  RunDetail,
  Decision,
  Candidate,
  AbstractInstantiation,
  IndexedInstantiation,
  ProvenanceRow,
  EvalRunsIndex,
  EvalRunManifest,
  LaunchEvalRunRequest,
  EvalRunActionResult,
} from "./types";

const BASE = "/api";

async function get<T>(path: string): Promise<T> {
  const res = await fetch(`${BASE}${path}`);
  if (!res.ok) throw new Error(`${res.status} ${res.statusText}`);
  return res.json();
}

async function post<T>(path: string, body?: unknown): Promise<T> {
  const res = await fetch(`${BASE}${path}`, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: body == null ? undefined : JSON.stringify(body),
  });
  if (!res.ok) {
    const payload = await res.json().catch(() => null);
    const message =
      payload && typeof payload.error === "string"
        ? payload.error
        : `${res.status} ${res.statusText}`;
    throw new Error(message);
  }
  return res.json();
}

export const api = {
  benchmarks: () => get<BenchmarkSummary[]>("/benchmarks"),

  runs: (benchmarkName: string) =>
    get<RunSummary[]>(`/benchmarks/${encodeURIComponent(benchmarkName)}/runs`),

  runSummary: (id: number) => get<RunDetail>(`/runs/${id}/summary`),

  decisions: (id: number) => get<Decision[]>(`/runs/${id}/decisions`),

  candidates: (runId: number, decisionId: number) =>
    get<Candidate[]>(`/runs/${runId}/decisions/${decisionId}/candidates`),

  abstractInstantiations: (id: number) =>
    get<AbstractInstantiation[]>(`/runs/${id}/abstract-instantiations`),

  indexedInstantiations: (id: number) =>
    get<IndexedInstantiation[]>(`/runs/${id}/indexed-instantiations`),

  provenance: (id: number) =>
    get<ProvenanceRow[]>(`/runs/${id}/provenance`),

  evalRuns: () => get<EvalRunsIndex>("/eval-runs"),

  evalRun: (runId: string) =>
    get<EvalRunManifest>(`/eval-runs/${encodeURIComponent(runId)}`),

  launchEvalRun: (request: LaunchEvalRunRequest) =>
    post<EvalRunActionResult>("/eval-runs", request),

  refreshEvalRun: (runId: string) =>
    post<EvalRunActionResult>(`/eval-runs/${encodeURIComponent(runId)}/refresh`),

  downloadReport: (runId: string) =>
    post<EvalRunActionResult>(
      `/eval-runs/${encodeURIComponent(runId)}/download-report`,
    ),

  teardownSubrun: (runId: string, subrunIndex: number) =>
    post<EvalRunActionResult>(
      `/eval-runs/${encodeURIComponent(runId)}/subruns/${subrunIndex}/teardown`,
    ),
};
