import type {
  BenchmarkSummary,
  RunSummary,
  RunDetail,
  Decision,
  Candidate,
  AbstractInstantiation,
  IndexedInstantiation,
  ProvenanceRow,
} from "./types";

const BASE = "/api";

async function get<T>(path: string): Promise<T> {
  const res = await fetch(`${BASE}${path}`);
  if (!res.ok) throw new Error(`${res.status} ${res.statusText}`);
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
};
