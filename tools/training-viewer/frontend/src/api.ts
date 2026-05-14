import type {
  BenchmarkSummary,
  RunSummary,
  RunDetail,
  Decision,
  Candidate,
  AbstractInstantiation,
  IndexedInstantiation,
  ProvenanceRow,
  TrainingDatabaseId,
  TrainingDatabaseOption,
  EvalRunsIndex,
  EvalRunManifest,
  LaunchEvalRunRequest,
  EvalRunActionResult,
} from "./types";

const BASE = "/api";

function withDatabase(path: string, database?: TrainingDatabaseId): string {
  if (!database) return path;
  const separator = path.includes("?") ? "&" : "?";
  return `${path}${separator}db=${encodeURIComponent(database)}`;
}

async function get<T>(
  path: string,
  database?: TrainingDatabaseId,
): Promise<T> {
  const res = await fetch(`${BASE}${withDatabase(path, database)}`);
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
  trainingDatabases: () =>
    get<TrainingDatabaseOption[]>("/training-databases"),

  benchmarks: (database: TrainingDatabaseId) =>
    get<BenchmarkSummary[]>("/benchmarks", database),

  runs: (benchmarkName: string, database: TrainingDatabaseId) =>
    get<RunSummary[]>(
      `/benchmarks/${encodeURIComponent(benchmarkName)}/runs`,
      database,
    ),

  runSummary: (id: number, database: TrainingDatabaseId) =>
    get<RunDetail>(`/runs/${id}/summary`, database),

  decisions: (id: number, database: TrainingDatabaseId) =>
    get<Decision[]>(`/runs/${id}/decisions`, database),

  candidates: (
    runId: number,
    decisionId: number,
    database: TrainingDatabaseId,
  ) =>
    get<Candidate[]>(
      `/runs/${runId}/decisions/${decisionId}/candidates`,
      database,
    ),

  abstractInstantiations: (id: number, database: TrainingDatabaseId) =>
    get<AbstractInstantiation[]>(
      `/runs/${id}/abstract-instantiations`,
      database,
    ),

  indexedInstantiations: (id: number, database: TrainingDatabaseId) =>
    get<IndexedInstantiation[]>(
      `/runs/${id}/indexed-instantiations`,
      database,
    ),

  provenance: (id: number, database: TrainingDatabaseId) =>
    get<ProvenanceRow[]>(`/runs/${id}/provenance`, database),

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
