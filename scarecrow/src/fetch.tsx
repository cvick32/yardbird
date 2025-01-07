import { Octokit } from "@octokit/core";
import { useQuery } from "@tanstack/react-query";
import JSZip from "jszip";
import { useAuth } from "./AuthProvider";

export interface Artifact {
  benchmarks: Benchmark[] | undefined;
  id: string;
  commitSha: string;
}

export interface Benchmark {
  example: string;
  result: BenchmarkResult;
}

export type BenchmarkResult =
  | { Success: Success }
  | { Timeout: number }
  | { Error: String }
  | { Panic: String };

export interface Success {
  used_instances: string[];
  const_instances: string[];
}

export function isSuccess(result: BenchmarkResult) {
  if ("Success" in result) {
    return result.Success.used_instances.length !== 0;
  } else {
    return false;
  }
}

export function isTrivial(result: BenchmarkResult) {
  if ("Success" in result) {
    return result.Success.used_instances.length === 0;
  } else {
    return false;
  }
}

export function isTimeout(result: BenchmarkResult) {
  return "Timeout" in result;
}

export function isError(result: BenchmarkResult) {
  return "Error" in result;
}

export function isPanic(result: BenchmarkResult) {
  return "Panic" in result;
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

export function useArtifact<T = Artifact>(
  id?: string,
  select?: (x: Artifact) => T,
  enabled: boolean = true,
) {
  const auth = useAuth();
  const octokit = new Octokit({
    auth: auth.token,
  });
  return useQuery({
    queryKey: ["artifacts", `${id}`],
    queryFn: async () => fetchArtifact(octokit, id!),
    staleTime: 60 * 1000, // 1 minute
    select,
    enabled: enabled && !!id,
  });
}

export function useCommitMessage(commitSha: string) {
  const auth = useAuth();
  const octokit = new Octokit({
    auth: auth.token,
  });
  return useQuery({
    queryKey: ["commit", `${commitSha}`],
    queryFn: async () => fetchGitCommitMessage(octokit, commitSha),
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
      res.data.workflow_runs.filter((run: any) => run.status !== "completed"),
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
    return {
      benchmarks: JSON.parse(garden) as Benchmark[],
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
  return octokit.request("GET /repos/{owner}/{repo}/actions/runs?per_page=1", {
    owner: "cvick32",
    repo: "yardbird",
    headers: {
      "X-GitHub-Api-Version": "2022-11-28",
    },
  });
}

export function benchmarkSummary(artifact: Artifact) {
  let success = 0;
  let trivialSuccess = 0;
  let timeout = 0;
  let error = 0;
  let panic = 0;

  if (artifact.benchmarks !== undefined) {
    for (const b of artifact.benchmarks) {
      const res = b.result;
      if ("Success" in res) {
        if (res.Success.used_instances.length === 0) {
          trivialSuccess += 1;
        } else {
          success += 1;
        }
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
    trivialSuccess,
    timeout,
    error,
    panic,
  };
}
