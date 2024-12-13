import { Octokit } from "@octokit/core";
import { useQuery } from "@tanstack/react-query";
import JSZip from "jszip";

const octokit = new Octokit({
  auth: `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`,
});

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

export function useArtifacts() {
  return useQuery({
    queryKey: ["artifacts"],
    queryFn: fetchArtifacts,
    staleTime: 60 * 1000, // 1 minute
  });
}

export function useArtifact<T = Benchmark[] | undefined>(
  id: string,
  select?: (x: Benchmark[] | undefined) => T,
) {
  return useQuery({
    queryKey: ["artifacts", `${id}`],
    queryFn: async () => fetchArtifact(id),
    staleTime: 60 * 1000, // 1 minute
    select,
  });
}

async function fetchArtifacts() {
  return octokit.request("GET /repos/{owner}/{repo}/actions/artifacts/", {
    owner: "cvick32",
    repo: "yardbird",
    headers: {
      "X-GitHub-Api-Version": "2022-11-28",
    },
  });
}

async function fetchArtifact(id: string): Promise<Benchmark[] | undefined> {
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

  const z = await JSZip.loadAsync(res.data);
  const garden = await z.file("garden.json")?.async("string");
  if (garden) {
    return JSON.parse(garden) as Benchmark[];
  } else {
    return undefined;
  }
}

export function benchmarkSummary(benchmarks?: Benchmark[]) {
  let success = 0;
  let trivialSuccess = 0;
  let timeout = 0;
  let error = 0;
  let panic = 0;

  if (benchmarks !== undefined) {
    for (const b of benchmarks) {
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
