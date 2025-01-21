import { createFileRoute, redirect } from "@tanstack/react-router";
import { useState } from "react";
import {
  Benchmark,
  getResult,
  getStatus,
  useArtifact,
  useProblem,
} from "../../fetch";

export const Route = createFileRoute("/artifacts/$art_/$problem_")({
  beforeLoad: ({ context }) => {
    if (!context.auth.isAuthenticated) {
      throw redirect({ to: "/oauth" });
    }
  },
  component: RouteComponent,
});

function RouteComponent() {
  const { problem: problemRaw } = Route.useParams();
  const problem = problemRaw.replaceAll("--", "/");

  return (
    <div className="flex flex-col place-items-start gap-2">
      <ResultView />
      <ProblemView problem={problem} />
      <Instances />
    </div>
  );
}

function ProblemView({ problem }: { problem: string }) {
  const [encoding, setEncoding] = useState("VMT");
  let vmtQuery = useProblem(problem);

  return (
    <>
      <div className="pl-5 text-lg font-bold text-black dark:text-white">
        Program Encodings:
      </div>

      <div>
        <div className="flex flex-row gap-2 text-lg">
          <button
            onClick={() => setEncoding("VMT")}
            className={[
              "border-black bg-slate-300",
              encoding === "VMT" && "border-8",
            ].join(" ")}
          >
            VMT
          </button>
          <button
            onClick={() => setEncoding("Rust")}
            className={[
              "border-black bg-slate-300",
              encoding === "Rust" && "border-8",
            ].join(" ")}
          >
            Rust
          </button>
        </div>
        {encoding === "VMT" &&
        !!vmtQuery.data &&
        "content" in vmtQuery.data.data ? (
          <textarea
            cols={80}
            rows={25}
            readOnly={true}
            className="bg-solarized-base3 text-solarized-base00 dark:bg-solarized-base03 dark:text-solarized-base0 grow-0 whitespace-pre-line font-mono"
          >
            {window.atob(vmtQuery.data.data.content)}
          </textarea>
        ) : (
          "rust code..."
        )}
      </div>
    </>
  );
}

function ResultView() {
  const { art, problem: problemRaw } = Route.useParams();
  const problem = problemRaw.replaceAll("--", "/");

  const benchmark = useArtifact(art, (artifact) =>
    artifact.benchmarks?.find((bench) => bench.example === problem),
  );

  if (benchmark.isPending) {
    return <div>Loading results...</div>;
  }

  if (!benchmark.data || benchmark.isError) {
    return <div>Error! {JSON.stringify(benchmark.error)}</div>;
  }

  return (
    <>
      <table>
        <tr className="divide-x divide-slate-400 border border-slate-400 bg-slate-200 text-black dark:divide-slate-600 dark:border-slate-600 dark:bg-slate-700 dark:text-white">
          <th className="px-2 font-bold">Strategy</th>
          <th className="px-2 font-bold">Status</th>
          <th className="px-2 font-bold">Depth</th>
          <th className="px-2 font-bold">Runtime (ms)</th>
        </tr>
        <ResultRow benchmark={benchmark.data} />
      </table>
    </>
  );
}

function ResultRow({ benchmark }: { benchmark: Benchmark }) {
  if (Array.isArray(benchmark.result)) {
    return (
      <>
        {benchmark.result.map((res) => (
          <tr className="divide-x divide-slate-400 border border-slate-400 text-black dark:divide-slate-600 dark:border-slate-600 dark:text-white">
            <td className="px-2">{res.strategy}</td>
            <td className="px-2">{getStatus(res.result)}</td>
            <td className="px-2">{res.depth}</td>
            <td className="px-2">{res.run_time}ms</td>
          </tr>
        ))}
      </>
    );
  } else {
    return (
      <tr className="divide-x divide-slate-400 border border-slate-400 dark:divide-slate-600 dark:border-slate-600">
        <td className="px-2">Abstract</td>
        <td className="px-2">-</td>
        <td className="px-2">-</td>
        <td className="px-2">-</td>
      </tr>
    );
  }
}

function Instances() {
  const { art, problem: problemRaw } = Route.useParams();
  const problem = problemRaw.replaceAll("--", "/");

  const benchmark = useArtifact(art, (artifact) =>
    artifact.benchmarks?.find((bench) => bench.example === problem),
  );

  if (benchmark.isPending) {
    return <div>Loading results...</div>;
  }

  if (!benchmark.data || benchmark.isError) {
    return <div>Error! {JSON.stringify(benchmark.error)}</div>;
  }

  const result = getResult(benchmark.data);
  if (result === undefined) {
    return undefined;
  }

  if ("Success" in result) {
    return (
      <>
        <div className="pl-5 text-lg font-bold text-black dark:text-white">
          Used Instances:
        </div>
        <textarea
          cols={80}
          rows={10}
          readOnly={true}
          className="bg-solarized-base3 text-solarized-base00 dark:bg-solarized-base03 dark:text-solarized-base0 grow-0 whitespace-pre-line font-mono"
        >
          {result.Success.used_instances.join("\n\n")}
        </textarea>
      </>
    );
  }
  if ("NoProgress" in result) {
    return (
      <>
        <div>Used Instances:</div>
        <div>
          {result.NoProgress.used_instances.map((inst, idx) => (
            <div key={idx}>{inst}</div>
          ))}
        </div>
      </>
    );
  }
}
