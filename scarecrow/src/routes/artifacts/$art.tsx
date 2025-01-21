import { createFileRoute, Link, redirect } from "@tanstack/react-router";
import {
  Benchmark,
  BenchmarkResult,
  getResult,
  getRuntime,
  isError,
  isNoProgress,
  isPanic,
  isSuccess,
  isTimeout,
  isTrivial,
  useArtifact,
} from "../../fetch";
import { useState } from "react";
import { FaCaretDown, FaCaretRight } from "react-icons/fa6";

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
        <tbody className="divide-y divide-slate-300 dark:divide-slate-700">
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
              <Row benchmark={benchmark} index={idx} />
            ))}
        </tbody>
      </table>
    </div>
  );
}

function Row({ benchmark, index }: { benchmark: Benchmark; index: number }) {
  const [showInstances, setShowInstances] = useState(false);
  const { art } = Route.useParams();
  const { compare } = Route.useSearch();
  const compareAgainst = useArtifact(compare);
  const benchResult = getResult(benchmark);
  const benchmarkSuccess =
    benchResult !== undefined &&
    (("Success" in benchResult &&
      benchResult.Success.used_instances.length !== 0) ||
      ("NoProgress" in benchResult &&
        benchResult.NoProgress.used_instances.length !== 0));

  const compareResult = getResult(compareAgainst.data?.benchmarks?.[index]);
  const compareSuccess =
    compare !== "" &&
    compareResult !== undefined &&
    (("Success" in compareResult &&
      compareResult.Success.used_instances.length !== 0) ||
      ("NoProgress" in compareResult &&
        compareResult.NoProgress.used_instances.length !== 0));
  const isSuccess = benchmarkSuccess || compareSuccess;

  return (
    <tr className="divide-x divide-slate-300 text-black dark:divide-slate-700 dark:text-white">
      <td className="px-2 text-left align-top">
        <button
          className="flex w-full flex-row items-center gap-1"
          onClick={() => {
            if (isSuccess) {
              setShowInstances(!showInstances);
            }
          }}
        >
          <div className="w-4">
            {isSuccess && (showInstances ? <FaCaretDown /> : <FaCaretRight />)}
          </div>

          {benchmark.example}
        </button>
        <div className="ml-5 flex flex-row items-center gap-1">
          <Link
            to="/problem/$problem"
            params={{ problem: benchmark.example }}
            search={{ idx: index, art }}
            className="text-sm text-blue-500 hover:text-blue-600 hover:underline dark:text-blue-400 dark:hover:text-blue-500"
          >
            Details
          </Link>

          {!!getRuntime(benchmark) && (
            <>
              <span className="text-sm">{getRuntime(benchmark)}ms</span>
              {compare !== "" &&
                !!compareAgainst.data &&
                !!compareAgainst.data.benchmarks &&
                !!getRuntime(compareAgainst.data.benchmarks[index]) && (
                  <>
                    <span className="text-sm">
                      - {getRuntime(compareAgainst.data.benchmarks[index])}ms
                    </span>
                    <span className="text-sm">
                      ={" "}
                      {getRuntime(benchmark)! -
                        getRuntime(compareAgainst.data.benchmarks[index])!}
                      ms
                    </span>
                  </>
                )}
            </>
          )}
        </div>
      </td>
      <Status result={getResult(benchmark)} showInstances={showInstances} />
      {compare !== "" &&
        !!compareAgainst.data &&
        !!compareAgainst.data.benchmarks && (
          <Status
            result={getResult(compareAgainst.data.benchmarks[index])}
            showInstances={showInstances}
          />
        )}
    </tr>
  );
}

function Status({
  result,
  showInstances,
}: {
  result?: BenchmarkResult;
  showInstances: boolean;
}) {
  if (result === undefined) {
    return undefined;
  }

  if ("Success" in result) {
    if (result.Success.used_instances.length == 0) {
      return (
        <td className="m-0 bg-teal-200 px-2 text-left align-top dark:bg-teal-700">
          Trivial Success...something is wrong.
        </td>
      );
    } else {
      return (
        <td className="m-0 bg-green-200 px-2 text-left align-top dark:bg-green-800">
          Success!
          {showInstances && (
            <>
              <div>Used instances:</div>
              <div className="ml-2 max-w-[32vw] overflow-scroll font-mono">
                {result.Success.used_instances.map((inst, idx) => (
                  <div key={idx} className="text-nowrap">
                    {prettyPrint(parseSexp(inst))}
                  </div>
                ))}
              </div>
            </>
          )}
        </td>
      );
    }
  }

  if ("NoProgress" in result) {
    return (
      <td className="m-0 bg-pink-200 px-2 text-left align-top dark:bg-pink-800">
        No Progress!
        {showInstances && (
          <>
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
          </>
        )}
      </td>
    );
  }

  if ("Timeout" in result) {
    return (
      <td className="m-0 bg-orange-200 px-2 text-left align-top dark:bg-orange-700">
        Timed out after {result.Timeout / 1000}s
      </td>
    );
  }

  if ("Error" in result) {
    return (
      <td className="m-0 bg-red-200 px-2 text-left align-top dark:bg-red-800">
        {result.Error}
      </td>
    );
  }

  if ("Panic" in result) {
    return (
      <td className="m-0 bg-purple-200 px-2 text-left align-top dark:bg-purple-800">
        {result.Panic}
      </td>
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
