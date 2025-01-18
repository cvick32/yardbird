import { createFileRoute, Link, redirect } from "@tanstack/react-router";
import {
  Benchmark,
  BenchmarkResult,
  isError,
  isNoProgress,
  isPanic,
  isSuccess,
  isTimeout,
  isTrivial,
  useArtifact,
} from "../../fetch";

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
    return <div>Loading Artifacts...</div>;
  }

  if (!artifact.data || artifact.isError) {
    return <div>Error! {JSON.stringify(artifact.error)}</div>;
  }

  return (
    <div>
      <table className="relative">
        <thead>
          <tr className="divide-x divide-slate-400 dark:divide-slate-600">
            <th
              className={`bg-slate-300 font-bold dark:bg-slate-700 dark:text-white`}
            >
              Benchmark
            </th>
            <th
              className={`z-[1000] bg-slate-300 font-bold dark:bg-slate-700 dark:text-white`}
            >
              Status
            </th>
            {compare !== "" && !!compareAgainst && (
              <th
                className={`z-[1000] bg-slate-300 font-bold dark:bg-slate-700 dark:text-white`}
              >
                Compare
              </th>
            )}
          </tr>
        </thead>
        <tbody className="divide-y divide-slate-400 dark:divide-slate-600">
          {artifact.data.benchmarks
            ?.map((benchmark, idx) => [benchmark, idx] as [Benchmark, number])
            .filter(([benchmark, idx]) => {
              if (filter === "") {
                return true;
              } else if (filter === "success") {
                return isSuccess(benchmark.result);
              } else if (filter === "noProgress") {
                return isNoProgress(benchmark.result);
              } else if (filter === "trivial") {
                return isTrivial(benchmark.result);
              } else if (filter === "timeout") {
                return isTimeout(benchmark.result);
              } else if (filter === "error") {
                return isError(benchmark.result);
              } else if (filter === "panic") {
                return isPanic(benchmark.result);
              } else if (filter === "differ") {
                return (
                  !!compareAgainst.data &&
                  !!compareAgainst.data.benchmarks &&
                  !(
                    isSuccess(benchmark.result) &&
                    isSuccess(compareAgainst.data.benchmarks[idx].result)
                  ) &&
                  !(
                    isNoProgress(benchmark.result) &&
                    isNoProgress(compareAgainst.data.benchmarks[idx].result)
                  ) &&
                  !(
                    isTrivial(benchmark.result) &&
                    isTrivial(compareAgainst.data.benchmarks[idx].result)
                  ) &&
                  !(
                    isTimeout(benchmark.result) &&
                    isTimeout(compareAgainst.data.benchmarks[idx].result)
                  ) &&
                  !(
                    isError(benchmark.result) &&
                    isError(compareAgainst.data.benchmarks[idx].result)
                  ) &&
                  !(
                    isPanic(benchmark.result) &&
                    isPanic(compareAgainst.data.benchmarks[idx].result)
                  )
                );
              } else {
                return false;
              }
            })
            .map(([benchmark, idx]) => (
              <tr key={idx} className="text-black dark:text-white">
                <td className="text-left align-top">
                  <Link
                    to="/problem/$problem"
                    params={{ problem: benchmark.example }}
                    search={{ idx: idx, art: art }}
                    className="text-blue-500 hover:text-blue-600 hover:underline dark:text-blue-400 dark:hover:text-blue-500"
                  >
                    {benchmark.example}
                  </Link>
                </td>
                <td className="text-left align-top">
                  <Status result={benchmark.result} />
                </td>
                {compare != "" &&
                  !!compareAgainst.data &&
                  !!compareAgainst.data.benchmarks && (
                    <td className="text-left align-top">
                      <Status
                        result={compareAgainst.data.benchmarks[idx]?.result}
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

function Status({ result }: { result?: BenchmarkResult }) {
  if (result === undefined) {
    return undefined;
  }

  if ("Success" in result) {
    if (result.Success.used_instances.length == 0) {
      return (
        <div className="bg-teal-200 dark:bg-teal-700">
          Trivial Success...something is wrong.
        </div>
      );
    } else {
      return (
        <div className="bg-green-200 dark:bg-green-800">
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

  if ("NoProgress" in result) {
    return (
      <div className="bg-pink-200 dark:bg-pink-800">
        No Progress!
        <div>Used instances:</div>
        <div className="ml-2 font-mono">
          {result.NoProgress.used_instances.map((inst, idx) => (
            <div key={idx}>{prettyPrint(parseSexp(inst))}</div>
          ))}
        </div>
        <div>Const instances:</div>
        <div className="ml-2 font-mono">
          {result.NoProgress.const_instances.map((inst, idx) => (
            <div key={idx}>{inst}</div>
          ))}
        </div>
      </div>
    );
  }

  if ("Timeout" in result) {
    return (
      <div className="bg-orange-200 dark:bg-orange-700">
        Timed out after {result.Timeout / 1000}s
      </div>
    );
  }

  if ("Error" in result) {
    return <div className="bg-red-200 dark:bg-red-800">{result.Error}</div>;
  }

  if ("Panic" in result) {
    return (
      <div className="bg-purple-200 dark:bg-purple-800">{result.Panic}</div>
    );
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
