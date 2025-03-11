import { Octokit } from "@octokit/core";
import { useQuery } from "@tanstack/react-query";
import JSZip from "jszip";
import { useAuth } from "./AuthProvider";
import { useFiles } from "./FileProvider";

export interface Artifact {
  benchmarks: Benchmark[] | undefined;
  id: string;
  commitSha: string;
}

export interface Benchmark {
  example: string;
  result: BenchmarkResult | StrategyResult[];
}

export type BenchmarkResult =
  | { Success: ProofLoopResult }
  | { NoProgress: ProofLoopResult }
  | { FoundProof: ProofLoopResult }
  | { Timeout: number }
  | { Error: string }
  | { Panic: string };

export interface StrategyResult {
  strategy: string;
  result: BenchmarkResult;
  run_time: number;
  depth: number;
}

export interface ProofLoopResult {
  used_instances: string[];
  const_instances: string[];
}

export function getResult(
  benchmark?: Benchmark,
  strat: string = "abstract",
): BenchmarkResult | undefined {
  if (benchmark === undefined) return undefined;

  if (Array.isArray(benchmark.result)) {
    return benchmark.result.find((res) => res.strategy === strat)?.result;
  } else {
    return benchmark.result;
  }
}

export function getRuntime(
  benchmark?: Benchmark,
  strat: string = "abstract",
): number | undefined {
  if (benchmark === undefined) return undefined;
  if (Array.isArray(benchmark.result)) {
    return benchmark.result.find((res) => res.strategy === strat)?.run_time;
  } else {
    return undefined;
  }
}

export function getStatus(result?: BenchmarkResult): string {
  if (result === undefined) {
    return "";
  } else if ("Success" in result) {
    if (result.Success.used_instances.length > 0) {
      return "success";
    } else {
      return "trivial";
    }
  } else if ("FoundProof" in result) {
    return "found-proof";
  } else if ("NoProgress" in result) {
    return "no-progress";
  } else if ("Timeout" in result) {
    return "timeout";
  } else if ("Error" in result) {
    return "error";
  } else if ("Panic" in result) {
    return "panic";
  } else {
    return "nyi";
  }
}

function benchmarkVariant(
  test: (res: BenchmarkResult) => boolean,
  result?: BenchmarkResult | StrategyResult[],
  strat: string = "abstract",
) {
  console.log("bv", result);
  if (result === undefined) {
    return false;
  } else if (Array.isArray(result)) {
    return benchmarkVariant(
      test,
      result.find((res) => res.strategy === strat)?.result,
      strat,
    );
  } else {
    return test(result);
  }
}

export function isSuccess(
  result?: BenchmarkResult | StrategyResult[],
  strat: string = "abstract",
) {
  return benchmarkVariant(
    (res) => "Success" in res && res.Success.used_instances.length > 0,
    result,
    strat,
  );
}

export function isFoundProof(
  result?: BenchmarkResult | StrategyResult[],
  strat: string = "abstract",
) {
  return benchmarkVariant((res) => "FoundProof" in res, result, strat);
}

export function isNoProgress(
  result?: BenchmarkResult | StrategyResult[],
  strat: string = "abstract",
) {
  return benchmarkVariant((res) => "NoProgress" in res, result, strat);
}

export function isTrivial(
  result?: BenchmarkResult | StrategyResult[],
  strat: string = "abstract",
) {
  return benchmarkVariant(
    (res) => "Success" in res && res.Success.used_instances.length === 0,
    result,
    strat,
  );
}

export function isTimeout(
  result?: BenchmarkResult | StrategyResult[],
  strat: string = "abstract",
) {
  return benchmarkVariant((res) => "Timeout" in res, result, strat);
}

export function isError(
  result: BenchmarkResult | StrategyResult[],
  strat: string = "abstract",
) {
  return benchmarkVariant((res) => "Error" in res, result, strat);
}

export function isPanic(
  result: BenchmarkResult | StrategyResult[],
  strat: string = "abstract",
) {
  return benchmarkVariant((res) => "Panic" in res, result, strat);
}

export function useArtifacts() {
  const auth = useAuth();
  const octokit = new Octokit({
    auth: auth.token,
  });
  return useQuery({
    queryKey: ["artifacts"],
    queryFn: async () => fetchArtifacts(octokit),
    staleTime: 0,
  });
}

export function useProblem(problemName: string) {
  const auth = useAuth();
  const octokit = new Octokit({
    auth: auth.token,
  });
  return useQuery({
    queryKey: ["problem", `${problemName}`],
    queryFn: async () => fetchProblem(octokit, problemName),
    staleTime: 60 * 1000,
  });
}

export function useArtifact<T = Artifact>(
  id?: string,
  select?: (x: Artifact) => T,
  enabled: boolean = true,
) {
  const auth = useAuth();
  const octokit = new Octokit({
    auth: auth.token,
  });
  const { files } = useFiles();

  if (id?.toString().startsWith("local:")) {
    return useQuery({
      queryKey: ["artifacts", `${id}`],
      queryFn: () =>
        files.get(id) ?? {
          benchmarks: [],
          id: "",
          commitSha: "",
        },
      staleTime: 60 * 1000, // 1 minute
      select,
      enabled: enabled && !!id,
    });
  } else {
    return useQuery({
      queryKey: ["artifacts", `${id}`],
      queryFn: async () => fetchArtifact(octokit, id!),
      staleTime: 60 * 1000, // 1 minute
      select,
      enabled: enabled && !!id,
    });
  }
}

export function useCommitMessage(commitSha: string) {
  const auth = useAuth();
  const octokit = new Octokit({
    auth: auth.token,
  });
  return useQuery({
    queryKey: ["commit", `${commitSha}`],
    queryFn: async () => {
      if (commitSha === "") {
        return "";
      } else {
        return fetchGitCommitMessage(octokit, commitSha);
      }
    },
    staleTime: 60 * 1000, // 1 minute
  });
}

export function useInProgressWorkflows() {
  const auth = useAuth();
  const octokit = new Octokit({
    auth: auth.token,
  });
  return useQuery({
    queryKey: ["workflows"],
    queryFn: async () => fetchWorkflows(octokit),
    select: (res) =>
      res.data.workflow_runs.filter(
        (run: any) => run.status !== "completed" && run.name === "Garden",
      ),
    refetchInterval: 10 * 1000, // 10 seconds
  });
}

async function fetchArtifacts(octokit: Octokit) {
  return octokit.request("GET /repos/{owner}/{repo}/actions/artifacts/", {
    owner: "cvick32",
    repo: "yardbird",
    headers: {
      "X-GitHub-Api-Version": "2022-11-28",
    },
  });
}

export async function fetchArtifact(octokit: Octokit, id: string) {
  let res = await octokit.request(
    `GET /repos/{owner}/{repo}/actions/artifacts/${id}/zip`,
    {
      owner: "cvick32",
      repo: "yardbird",
      headers: {
        "X-GitHub-Api-Version": "2022-11-28",
      },
    },
  );

  let artifactInfo = await octokit.request(
    `GET /repos/{owner}/{repo}/actions/artifacts/${id}`,
    {
      owner: "cvick32",
      repo: "yardbird",
      headers: {
        "X-GitHub-Api-Version": "2022-11-28",
      },
    },
  );

  const z = await JSZip.loadAsync(res.data);
  const garden = await z.file("garden.json")?.async("string");
  if (garden) {
    const benchmarks = JSON.parse(garden) as Benchmark[];
    benchmarks.sort((a, b) => (a.example < b.example ? -1 : 1));
    return {
      benchmarks,
      id,
      commitSha: artifactInfo.data.workflow_run.head_sha,
    };
  } else {
    return {
      benchmarks: undefined,
      id,
      commitSha: artifactInfo.data.workflow_run.head_sha,
    };
  }
}

async function fetchProblem(octokit: Octokit, problemName: string) {
  return octokit.request("GET /repos/{owner}/{repo}/contents/{path}", {
    owner: "cvick32",
    repo: "yardbird",
    path: problemName,
    headers: {
      "X-GitHub-Api-Version": "2022-11-28",
    },
  });
}

async function fetchGitCommitMessage(octokit: Octokit, sha: string) {
  return octokit.request("GET /repos/{owner}/{repo}/commits/{ref}", {
    owner: "cvick32",
    repo: "yardbird",
    ref: sha,
    headers: {
      "X-GitHub-Api-Version": "2022-11-28",
    },
  });
}

async function fetchWorkflows(octokit: Octokit) {
  return octokit.request("GET /repos/{owner}/{repo}/actions/runs?per_page=2", {
    owner: "cvick32",
    repo: "yardbird",
    headers: {
      "X-GitHub-Api-Version": "2022-11-28",
    },
  });
}

export async function readFile(file: File): Promise<Artifact> {
  const text = await file.text();
  return {
    benchmarks: JSON.parse(text),
    id: `local:${file.name}`,
    commitSha: "",
  };
}

export function benchmarkSummary(artifact: Artifact) {
  let success = 0;
  let foundProof = 0;
  let noProgress = 0;
  let trivialSuccess = 0;
  let timeout = 0;
  let error = 0;
  let panic = 0;

  if (artifact.benchmarks !== undefined) {
    for (const b of artifact.benchmarks) {
      const res = getResult(b);
      if (res === undefined) {
        continue;
      } else if ("Success" in res) {
        if (res.Success.used_instances.length === 0) {
          trivialSuccess += 1;
        } else {
          success += 1;
        }
      } else if ("FoundProof" in res) {
        foundProof += 1;
      } else if ("NoProgress" in res) {
        noProgress += 1;
      } else if ("Timeout" in res) {
        timeout += 1;
      } else if ("Error" in res) {
        error += 1;
      } else if ("Panic" in res) {
        panic += 1;
      }
    }
  }

  return {
    success,
    foundProof,
    noProgress,
    trivialSuccess,
    timeout,
    error,
    panic,
  };
}

export function selectGeomean(filter: string = "", artifact: Artifact) {
  const speedups = artifact.benchmarks
    ?.filter(
      (benchmark) =>
        filter === "" || getStatus(getResult(benchmark)) === filter,
    )
    .flatMap((bench) => {
      const abstract = getRuntime(bench, "abstract");
      const concrete = getRuntime(bench, "concrete");
      if (!!abstract && !!concrete) {
        return [concrete / abstract];
      } else {
        return [];
      }
    });
  return (
    speedups &&
    Math.pow(
      speedups.reduce((a, b) => a * b),
      1 / speedups.length,
    )
  );
}
