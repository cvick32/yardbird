import { createFileRoute, redirect, useNavigate } from "@tanstack/react-router";
import {
  Benchmark,
  BenchmarkResult,
  fetchArtifact,
  useArtifact,
  useArtifacts,
} from "../../fetch";
import { useEffect, useState } from "react";
import { useAuth } from "../../AuthProvider";
import { Octokit } from "@octokit/core";

export const Route = createFileRoute("/artifacts/$art")({
  validateSearch: (search: Record<string, unknown>) => ({
    compare: (search.compare as string) || "",
  }),
  beforeLoad: ({ context }) => {
    if (!context.auth.isAuthenticated) {
      throw redirect({ to: "/oauth" });
    }
  },
  component: RouteComponent,
});

function RouteComponent() {
  const { art } = Route.useParams();
  const { compare } = Route.useSearch();
  const artifact = useArtifact(art);
  const artifacts = useArtifacts();
  const [compareAgainst, setCompareAgainst] = useState<Benchmark[] | undefined>(
    undefined,
  );
  const [filter, setFilter] = useState<string>("");
  const auth = useAuth();
  const navigate = useNavigate({ from: Route.fullPath });

  useEffect(() => {
    if (compare !== "") {
      const octokit = new Octokit({
        auth: auth.token,
      });
      fetchArtifact(octokit, compare).then(setCompareAgainst);
    }
  }, [compare]);

  if (artifact.isPending) {
    return <div>Loading...</div>;
  }

  if (!artifact.data || artifact.isError) {
    return <div>Error! {JSON.stringify(artifact.error)}</div>;
  }

  return (
    <div>
      <div>
        <label htmlFor="filter" className="mr-2 font-bold">
          Filter:
        </label>
        <select
          name="filter"
          onChange={(ev) => {
            setFilter(ev.target.value);
          }}
        >
          <option value="">None</option>
          <option value="success">Success</option>
          <option value="timeout">Timeout</option>
          <option value="error">Error</option>
          <option value="panic">Panic</option>
          <option value="differ">Differ</option>
        </select>
      </div>
      <div>
        <label htmlFor="compare" className="mr-2 font-bold">
          Compare:
        </label>
        <select
          name="compare"
          onChange={(ev) => {
            navigate({
              search: () => ({ compare: ev.target.value.trim() }),
            });
          }}
          defaultValue={compare}
        >
          <option value="">None</option>
          {!!artifacts.data &&
            artifacts.data.data.artifacts
              .filter((art: any) => `${art.id}` !== `${artifact.data.id}`)
              .map((art: any, idx: number) => {
                let date = new Date(Date.parse(art.created_at));
                let dayString = date.toLocaleDateString("en-US");
                return (
                  <option key={idx} value={art.id}>
                    {dayString} {`#${art.workflow_run.head_sha.slice(0, 7)}`}
                  </option>
                );
              })}
        </select>
      </div>
      <table className="border-collapse border border-slate-400">
        <thead>
          <tr>
            <th className="border border-slate-300 font-bold">Benchmark</th>
            <th className="border border-slate-300 font-bold">Status</th>
            {compare !== "" && !!compareAgainst && (
              <th className="border border-slate-300 font-bold">Compare</th>
            )}
          </tr>
        </thead>
        <tbody>
          {artifact.data.benchmarks
            ?.map((benchmark, idx) => [benchmark, idx] as [Benchmark, number])
            .filter(([benchmark, idx]) => {
              if (filter === "") {
                return true;
              } else if (filter === "success") {
                return "Success" in benchmark.result;
              } else if (filter === "timeout") {
                return "Timeout" in benchmark.result;
              } else if (filter === "error") {
                return "Error" in benchmark.result;
              } else if (filter === "panic") {
                return "Panic" in benchmark.result;
              } else if (filter === "differ") {
                return (
                  !!compareAgainst &&
                  !(
                    "Success" in benchmark.result &&
                    "Success" in compareAgainst[idx].result
                  ) &&
                  !(
                    "Timeout" in benchmark.result &&
                    "Timeout" in compareAgainst[idx].result
                  ) &&
                  !(
                    "Error" in benchmark.result &&
                    "Error" in compareAgainst[idx].result
                  ) &&
                  !(
                    "Panic" in benchmark.result &&
                    "Panic" in compareAgainst[idx].result
                  )
                );
              } else {
                return false;
              }
            })
            .map(([benchmark, idx]) => (
              <tr key={idx}>
                <th className="border border-slate-300 text-left align-top">
                  {benchmark.example}
                </th>
                <th className="border border-slate-300 text-left align-top">
                  <Status result={benchmark.result} />
                </th>
                {compare != "" && !!compareAgainst && (
                  <th className="border border-slate-300 text-left align-top">
                    <Status result={compareAgainst[idx].result} />
                  </th>
                )}
              </tr>
            ))}
        </tbody>
      </table>
    </div>
  );
}

function Status({ result }: { result: BenchmarkResult }) {
  if ("Success" in result) {
    if (result.Success.used_instances.length == 0) {
      return (
        <div className="bg-teal-200">
          Trivial Success...something is wrong.
          <div>Used instances:</div>
          <div className="ml-2 font-mono">
            {result.Success.used_instances.map((inst, idx) => (
              <div key={idx}>{inst}</div>
            ))}
          </div>
          <div>Const instances:</div>
          <div className="ml-2 font-mono">
            {result.Success.const_instances.map((inst, idx) => (
              <div key={idx}>{inst}</div>
            ))}
          </div>
        </div>
      );
    } else {
      return (
        <div className="bg-green-200">
          Success!
          <div>Used instances:</div>
          <div className="ml-2 font-mono">
            {result.Success.used_instances.map((inst, idx) => (
              <div key={idx}>{inst}</div>
            ))}
          </div>
          <div>Const instances:</div>
          <div className="ml-2 font-mono">
            {result.Success.const_instances.map((inst, idx) => (
              <div key={idx}>{inst}</div>
            ))}
          </div>
        </div>
      );
    }
  }

  if ("Timeout" in result) {
    return (
      <div className="bg-orange-200">
        Timed out after {result.Timeout / 1000}s
      </div>
    );
  }

  if ("Error" in result) {
    return <div className="bg-red-200">{result.Error}</div>;
  }

  if ("Panic" in result) {
    return <div className="bg-purple-200">{result.Panic}</div>;
  }
}
