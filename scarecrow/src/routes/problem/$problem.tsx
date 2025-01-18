import { createFileRoute, redirect } from "@tanstack/react-router";
import { Benchmark, useArtifact, useProblem } from "../../fetch";
import { useState } from "react";

export const Route = createFileRoute("/problem/$problem")({
  validateSearch: (search: Record<string, unknown>) => ({
    idx: +search.idx || 0,
    art: (search.artifact as string) || "",
  }),
  beforeLoad: ({ context }) => {
    if (!context.auth.isAuthenticated) {
      throw redirect({ to: "/oauth" });
    }
  },
  component: RouteComponent,
});

function RouteComponent() {
  const { problem } = Route.useParams();
  const { idx, art } = Route.useSearch();
  const [encoding, setEncoding] = useState("VMT");
  const artifact = useArtifact(art);
  let vmt_query = useProblem(problem);
  if (vmt_query.isPending || artifact.isPending) {
    return <div>Loading...</div>;
  }
  if (!vmt_query.data || vmt_query.isError || !artifact.data) {
    return <div>Error! {JSON.stringify(vmt_query.error)}</div>;
  }

  const name = problem.split("/")[1];
  const vmt_contents = window.atob(vmt_query.data.data.content);
  const benchmark = artifact.data.benchmarks[idx];

  return (
    <div className="flex flex-col items-center gap-5">
      <div className="self-start text-xl font-bold">Viewing {name}</div>
      <div className="self-start pl-5 text-lg font-bold">
        Program Encodings:
      </div>

      <div>
        <div className="flex flex-row gap-2 text-lg">
          <button
            onClick={() => setEncoding("Rust")}
            className={[
              "border-black bg-slate-300",
              encoding === "Rust" && "border-8",
            ].join(" ")}
          >
            Rust
          </button>
          <button
            onClick={() => setEncoding("VMT")}
            className={[
              "border-black bg-slate-300",
              encoding === "VMT" && "border-8",
            ].join(" ")}
          >
            VMT
          </button>
        </div>
        {encoding === "VMT" ? (
          <textarea
            cols={80}
            rows={25}
            readOnly={true}
            className="grow-0 whitespace-pre-line bg-[#FDF6E3] font-mono"
          >
            {vmt_contents}
          </textarea>
        ) : (
          "rust code..."
        )}
      </div>
      <Instances benchmark={benchmark} />
    </div>
  );
}

function Instances({ benchmark }: { benchmark: Benchmark }) {
  if ("Success" in benchmark.result) {
    return (
      <>
        <div className="self-start pl-5 text-lg font-bold">Used Instances:</div>
        <textarea
          cols={80}
          rows={10}
          readOnly={true}
          className="grow-0 whitespace-pre-line bg-[#FDF6E3] font-mono"
        >
          {benchmark.result.Success.used_instances.join("\n\n")}
        </textarea>
      </>
    );
  }
  if ("NoProgress" in benchmark.result) {
    return (
      <>
        <div>Used Instances:</div>
        <div>
          {benchmark.result.NoProgress.used_instances.map((inst, idx) => (
            <div key={idx}>{inst}</div>
          ))}
        </div>
      </>
    );
  }
}

function Runtime({ benchmark }: { benchmark: Benchmark }) {
  if ("Success" in benchmark.result) {
    return (
      <>
        <div>Used Instances:</div>
        <div>
          {benchmark.result.Success.used_instances.map((inst, idx) => (
            <div key={idx}>{inst}</div>
          ))}
        </div>
      </>
    );
  }
  if ("NoProgress" in benchmark.result) {
    return (
      <>
        <div>Used Instances:</div>
        <div>
          {benchmark.result.NoProgress.used_instances.map((inst, idx) => (
            <div key={idx}>{inst}</div>
          ))}
        </div>
      </>
    );
  }
}
