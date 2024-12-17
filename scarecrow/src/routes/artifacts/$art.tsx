import { createFileRoute, redirect } from "@tanstack/react-router";
import { BenchmarkResult, useArtifact } from "../../fetch";

export const Route = createFileRoute("/artifacts/$art")({
  beforeLoad: ({ context }) => {
    if (!context.auth.isAuthenticated) {
      throw redirect({ to: "/oauth" });
    }
  },
  component: RouteComponent,
});

function RouteComponent() {
  const { art } = Route.useParams();
  const artifact = useArtifact(art);

  if (artifact.isPending) {
    return <div>Loading...</div>;
  }

  if (!artifact.data || artifact.isError) {
    return <div>Error! {JSON.stringify(artifact.error)}</div>;
  }

  return (
    <table className="border-collapse border border-slate-400">
      <thead>
        <tr>
          <th className="border border-slate-300">Benchmark</th>
          <th className="border border-slate-300">Status</th>
        </tr>
      </thead>
      <tbody>
        {artifact.data.map((benchmark, idx) => (
          <tr key={idx}>
            <th className="border border-slate-300 text-left align-top">
              {benchmark.example}
            </th>
            <th className="border border-slate-300 text-left align-top">
              <Status result={benchmark.result} />
            </th>
          </tr>
        ))}
      </tbody>
    </table>
  );
}

function Status({ result }: { result: BenchmarkResult }) {
  if ("Success" in result) {
    if (result.Success.used_instances.length == 0) {
      return (
        <div className="bg-teal-200">
          Trivial Success...something is wrong.
          <div>Used instances:</div>
          <div className="font-mono ml-2">
            {result.Success.used_instances.map((inst, idx) => (
              <div key={idx}>{inst}</div>
            ))}
          </div>
          <div>Const instances:</div>
          <div className="font-mono ml-2">
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
          <div className="font-mono ml-2">
            {result.Success.used_instances.map((inst, idx) => (
              <div key={idx}>{inst}</div>
            ))}
          </div>
          <div>Const instances:</div>
          <div className="font-mono ml-2">
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
