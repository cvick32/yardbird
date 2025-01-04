import { createFileRoute, redirect } from "@tanstack/react-router";
import { Benchmark, BenchmarkResult, useArtifact } from "../../fetch";

export const Route = createFileRoute("/artifacts/$art")({
  validateSearch: (search: Record<string, unknown>) => ({
    compare: (search.compare as string) || "",
    filter: (search.filter as string) || "",
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
  const { compare, filter } = Route.useSearch();
  const artifact = useArtifact(art);
  const compareAgainst = useArtifact(compare);

  if (artifact.isPending) {
    return <div>Loading...</div>;
  }

  if (!artifact.data || artifact.isError) {
    return <div>Error! {JSON.stringify(artifact.error)}</div>;
  }

  return (
    <div>
      <table className="relative">
        <thead>
          <tr className="divide-x divide-slate-400">
            <th className="sticky top-[45px] z-10 bg-slate-300 font-bold">
              Benchmark
            </th>
            <th className="sticky top-[45px] z-10 bg-slate-300 font-bold">
              Status
            </th>
            {compare !== "" && !!compareAgainst && (
              <th className="sticky top-[44px] z-30 bg-slate-300 font-bold">
                Compare
              </th>
            )}
          </tr>
        </thead>
        <tbody className="divide-y divide-slate-300">
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
                  !!compareAgainst.data &&
                  !!compareAgainst.data.benchmarks &&
                  !(
                    "Success" in benchmark.result &&
                    "Success" in compareAgainst.data.benchmarks[idx].result
                  ) &&
                  !(
                    "Timeout" in benchmark.result &&
                    "Timeout" in compareAgainst.data.benchmarks[idx].result
                  ) &&
                  !(
                    "Error" in benchmark.result &&
                    "Error" in compareAgainst.data.benchmarks[idx].result
                  ) &&
                  !(
                    "Panic" in benchmark.result &&
                    "Panic" in compareAgainst.data.benchmarks[idx].result
                  )
                );
              } else {
                return false;
              }
            })
            .map(([benchmark, idx]) => (
              <tr key={idx}>
                <td className="text-left align-top">{benchmark.example}</td>
                <td className="text-left align-top">
                  <Status result={benchmark.result} />
                </td>
                {compare != "" &&
                  !!compareAgainst.data &&
                  !!compareAgainst.data.benchmarks && (
                    <td className="text-left align-top">
                      <Status
                        result={compareAgainst.data.benchmarks[idx].result}
                      />
                    </td>
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
            {result.Success.used_instances.map((inst, idx) => {
              return <div key={idx}>{inst}</div>;
            })}
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
              <div key={idx}>{prettyPrint(parseSexp(inst))}</div>
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

function parseSexp(str: string) {
  let tokens = tokenize(str);
  let index = 0;

  function tokenize(str: string): string[] {
    return str.replace(/\(/g, " ( ").replace(/\)/g, " ) ").trim().split(/\s+/);
  }

  function parse(): any[] | string {
    let token: string = tokens[index++];

    if (token === "(") {
      let list: (string | string[])[] = [];
      while (tokens[index] !== ")") {
        list.push(parse());
      }
      index++; // Skip closing parenthesis
      return list;
    } else if (token === ")") {
      throw new Error("Unexpected closing parenthesis");
    } else {
      return token;
    }
  }

  return parse();
}

function prettyPrint(inst: any[] | string): string {
  if (inst[0] === "=") {
    return prettyPrint(inst[1]) + " = " + prettyPrint(inst[2]);
  }

  if (inst[0] === "=>") {
    return `${prettyPrint(inst[1])} => (${prettyPrint(inst[2])})`;
  }

  if (inst[0] === "Read-Int-Int") {
    return `(read ${prettyPrint(inst[1])} ${prettyPrint(inst[2])})`;
  }

  if (inst[0] === "Write-Int-Int") {
    return `(write ${prettyPrint(inst[1])} ${prettyPrint(inst[2])} ${prettyPrint(inst[3])})`;
  }

  if (inst[0] === "not") {
    if (inst[1][0] === "=") {
      return `${prettyPrint(inst[1][1])} != ${prettyPrint(inst[1][2])}`;
    } else {
      return `(! (${prettyPrint(inst[1])}))`;
    }
  }

  if (Array.isArray(inst)) {
    const args = inst.slice(1).map((el) => prettyPrint(el));
    return `(${inst[0]} ${args.join(" ")})`;
  }

  return inst;
}
