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
  });
}

export function useArtifact(id: string) {
  return useQuery({
    queryKey: ["artifacts", id],
    queryFn: async () => fetchArtifact(id),
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
