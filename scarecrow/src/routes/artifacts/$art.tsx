import { createFileRoute, Link, redirect } from "@tanstack/react-router";
import {
  Artifact,
  Benchmark,
  BenchmarkResult,
  getResult,
  getRuntime,
  getStatus,
  selectGeomean,
  useArtifact,
} from "../../fetch";
import {
  YAxis,
  Tooltip,
  CartesianGrid,
  ResponsiveContainer,
  BarChart,
  Legend,
  Bar,
  Brush,
  ReferenceArea,
  XAxis,
  ScatterChart,
  Scatter,
  Cell,
  Label,
} from "recharts";
import { useState } from "react";
import { FaCaretDown, FaCaretRight } from "react-icons/fa6";

export const Route = createFileRoute("/artifacts/$art")({
  validateSearch: (search: Record<string, unknown>) => ({
    compare: (search.compare as string) || "",
    filter: (search.filter as string) || "",
    expand: (search.expand as boolean) || false,
    strategy: (search.strategy as string) || "abstract",
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
  const { compare, filter, strategy } = Route.useSearch();
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
      <div>
        <h1 style={{ textAlign: "center" }}>
          <b>Bounded Model Checking Speed Comparison</b>
        </h1>
        <div style={{ display: "flex", justifyContent: "center" }}>
          <SpeedUpGraph />
          <SpeedUpScatter />
        </div>
      </div>

      <ConflictGraph />
      <TimeSummary />
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
              } else if (filter === "differ") {
                return (
                  getStatus(getResult(benchmark, strategy)) !=
                  getStatus(
                    getResult(
                      compareAgainst?.data?.benchmarks?.[idx],
                      strategy,
                    ),
                  )
                );
              } else {
                return getStatus(getResult(benchmark, strategy)) === filter;
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

function TimeSummary() {
  const { art } = Route.useParams();
  const { filter } = Route.useSearch();
  const geomean = useArtifact(art, (artifact) =>
    selectGeomean(filter, artifact),
  );

  if (!geomean.data) return undefined;

  return (
    <div className="text-black dark:text-white">
      Average speedup (geomean concrete / abstract):{" "}
      {geomean.data > 1.0 ? (
        <span className="text-green-700 dark:text-green-300">
          {geomean.data.toFixed(2)}× faster
        </span>
      ) : (
        <span className="text-red-500">{geomean.data.toFixed(2)}× slower</span>
      )}
    </div>
  );
}

function getSuccessfulBenchmarks(artifact: Artifact): Benchmark[] {
  if (artifact.benchmarks === undefined) {
    return [];
  } else {
    return artifact.benchmarks?.filter(
      (benchmark) => getStatus(getResult(benchmark)) === "success",
    );
  }
}

function getConflicts(bench: BenchmarkResult): number {
  if ("Success" in bench) {
    const proofLoopResult = bench.Success;
    if (proofLoopResult.solver_statistics?.stats.conflicts === undefined) {
      return 0;
    } else {
      return proofLoopResult.solver_statistics?.stats.conflicts;
    }
  }
  return 0;
}

function ConflictGraph() {
  const { art } = Route.useParams();
  const artifact = useArtifact(art);

  if (artifact.isPending) {
    return <div>Loading Artifacts...</div>;
  }

  if (!artifact.data || artifact.isError) {
    return <div>Error! {JSON.stringify(artifact.error)}</div>;
  }
  try {
    const benchmarks: Benchmark[] = getSuccessfulBenchmarks(artifact.data);
    const data = benchmarks.flatMap((benchmark) => {
      if (benchmark.result[0].strategy === "abstract") {
        let abs_conflicts = getConflicts(benchmark.result[0].result);
        let con_conflicts = getConflicts(benchmark.result[1].result);
        return {
          example: benchmark.example, // Benchmark name
          abs_conflicts: abs_conflicts, // Abstract conflicts time
          con_conflicts: con_conflicts, // Concrete execution time
        };
      } else {
        let abs_conflicts = getConflicts(benchmark.result[1].result);
        let con_conflicts = getConflicts(benchmark.result[0].result);
        return {
          example: benchmark.example,
          abs_conflicts: abs_conflicts,
          con_conflicts: con_conflicts,
        };
      }
    });

    // Sort by difference in conflicts
    data.sort(
      (a, b) =>
        b.abs_conflicts - b.con_conflicts - (a.abs_conflicts - a.con_conflicts),
    );

    return (
      <div style={{ textAlign: "center", marginBottom: "20px" }}>
        <h2>Z3 Conflicts needed (Abstract vs Concrete)</h2>{" "}
        <ResponsiveContainer width="100%" height={400}>
          <BarChart
            data={data}
            margin={{ top: 20, right: 30, left: 20, bottom: 80 }}
          >
            <CartesianGrid strokeDasharray="3 3" />
            <YAxis />
            <XAxis dataKey="example" tick={false} axisLine={false} />
            <Tooltip
              content={
                <ConflictTooltip active={undefined} payload={undefined} />
              }
            />{" "}
            <Legend />
            {data.map((entry, index) => {
              return (
                <ReferenceArea
                  key={index}
                  x1={entry.example}
                  x2={
                    index < data.length - 1
                      ? data[index + 1].example
                      : entry.example
                  }
                  fill={getBackgroundColor(
                    entry.abs_conflicts,
                    entry.con_conflicts,
                  )}
                  fillOpacity={0.3}
                />
              );
            })}
            <Bar
              dataKey="abs_conflicts"
              name="Abstract Strategy"
              fill="#8884d8"
            />
            <Bar
              dataKey="con_conflicts"
              name="Concrete Strategy"
              fill="#82ca9d"
            />
            <Brush dataKey="id" height={20} stroke="#8884d8" />
            {/* Zoom & Scroll */}
          </BarChart>
        </ResponsiveContainer>
      </div>
    );
  } catch (error) {
    return (
      <div>
        <h3>No Solver Statistics...</h3>
      </div>
    );
  }
}

const ConflictTooltip = ({
  active,
  payload,
}: {
  active: any;
  payload: any;
}) => {
  if (active && payload && payload.length) {
    return (
      <div
        style={{
          background: "white",
          padding: "10px",
          border: "1px solid #ccc",
        }}
      >
        <p>
          <strong>Benchmark:</strong> {payload[0].payload.example}
        </p>
        <p>
          <strong>Abstract:</strong> {payload[0].payload.abs_conflicts}{" "}
          conflicts
        </p>
        <p>
          <strong>Concrete:</strong> {payload[0].payload.con_conflicts}{" "}
          conflicts
        </p>
      </div>
    );
  }
  return null;
};

const getScatterColor = (point: any) => {
  return point.abs_time > point.con_time ? "#f08080" : "#bcf5bc"; // Red if abstract > concrete, Green otherwise
};

function SpeedUpScatter() {
  const { art } = Route.useParams();
  const artifact = useArtifact(art);

  if (artifact.isPending) {
    return <div>Loading Artifacts...</div>;
  }

  if (!artifact.data || artifact.isError) {
    return <div>Error! {JSON.stringify(artifact.error)}</div>;
  }
  try {
    const benchmarks: Benchmark[] = getSuccessfulBenchmarks(artifact.data);
    const data = benchmarks.flatMap((benchmark) => {
      if (benchmark.result[0].strategy === "abstract") {
        let abs_time = benchmark.result[0].run_time;
        let con_time = benchmark.result[1].run_time;
        return {
          example: benchmark.example, // Benchmark name
          abs_time: abs_time / 1000, // Abstract execution time in seconds
          con_time: con_time / 1000, // Concrete execution time
        };
      } else {
        let abs_time = benchmark.result[1].run_time;
        let con_time = benchmark.result[0].run_time;
        return {
          example: benchmark.example, // Benchmark name
          abs_time: abs_time / 1000,
          con_time: con_time / 1000, // Execution time
        };
      }
    });

    const minVal = Math.min(
      ...data.map((d) => Math.min(d.con_time, d.abs_time)),
    );
    const maxVal = Math.max(
      ...data.map((d) => Math.max(d.con_time, d.abs_time)),
    );

    return (
      <ResponsiveContainer width="50%" height={400}>
        <ScatterChart margin={{ top: 20, right: 30, left: 20, bottom: 80 }}>
          <CartesianGrid />
          <XAxis
            type="number"
            dataKey="con_time"
            name="Concrete Time"
            scale="log"
            domain={[minVal, maxVal]}
          >
            <Label
              value="Concrete Runtime (s)"
              offset={-10}
              position="insideBottom"
            />
          </XAxis>
          <YAxis
            type="number"
            dataKey="abs_time"
            name="Abstract Time"
            scale="log"
            domain={[minVal, maxVal]}
          >
            <Label
              value="Abstract Runtime (s)"
              angle={-90}
              position="insideLeft"
              style={{ textAnchor: "middle" }}
            />
          </YAxis>
          <Scatter name="BMC Speed" data={data}>
            {data.map((entry, index) => (
              <Cell key={`cell-${index}`} fill={getScatterColor(entry)} />
            ))}
          </Scatter>
          <Tooltip
            content={<SpeedUpTooltip active={undefined} payload={undefined} />}
          />
        </ScatterChart>
      </ResponsiveContainer>
    );
  } catch (error) {
    return (
      <div>
        <h3>No Runtime Statistics...</h3>
      </div>
    );
  }
}

function SpeedUpGraph() {
  const { art } = Route.useParams();
  const artifact = useArtifact(art);

  if (artifact.isPending) {
    return <div>Loading Artifacts...</div>;
  }

  if (!artifact.data || artifact.isError) {
    return <div>Error! {JSON.stringify(artifact.error)}</div>;
  }
  try {
    const benchmarks: Benchmark[] = getSuccessfulBenchmarks(artifact.data);
    const data = benchmarks.flatMap((benchmark) => {
      if (benchmark.result[0].strategy === "abstract") {
        let abs_time = benchmark.result[0].run_time;
        let con_time = benchmark.result[1].run_time;
        return {
          example: benchmark.example, // Benchmark name
          abs_time: abs_time / 1000, // Abstract execution time
          con_time: con_time / 1000, // Concrete execution time
        };
      } else {
        let abs_time = benchmark.result[1].run_time;
        let con_time = benchmark.result[0].run_time;
        return {
          example: benchmark.example, // Benchmark name
          abs_time: abs_time / 1000,
          con_time: con_time / 1000, // Execution time
        };
      }
    });

    // Sort by difference in abstract and concrete times
    data.sort((a, b) => b.abs_time - b.con_time - (a.abs_time - a.con_time));

    return (
      <ResponsiveContainer width="50%" height={400}>
        <BarChart
          data={data}
          margin={{ top: 20, right: 30, left: 20, bottom: 80 }}
        >
          <CartesianGrid strokeDasharray="3 3" />
          <YAxis>
            {" "}
            <Label
              value="Runtime (s)"
              angle={-90}
              position="insideLeft"
              style={{ textAnchor: "middle" }}
            />
          </YAxis>
          <XAxis dataKey="example" tick={false} axisLine={false} />
          <Tooltip
            content={<SpeedUpTooltip active={undefined} payload={undefined} />}
          />
          <Legend />
          {/* Generate ReferenceArea for each bar dynamically */}
          {data.map((entry, index) => {
            console.log(`ReferenceArea for: ${entry.example}`);
            return (
              <ReferenceArea
                key={index}
                x1={entry.example}
                x2={
                  index < data.length - 1
                    ? data[index + 1].example
                    : entry.example
                }
                fill={getBackgroundColor(entry.abs_time, entry.con_time)}
                fillOpacity={0.3}
              />
            );
          })}
          <Bar dataKey="abs_time" name="Abstract Strategy" fill="#8884d8" />
          <Bar dataKey="con_time" name="Concrete Strategy" fill="#82ca9d" />
          <Brush dataKey="id" height={20} stroke="#8884d8" />
          {/* Zoom & Scroll */}
        </BarChart>
      </ResponsiveContainer>
    );
  } catch (error) {
    return (
      <div>
        <h3>No Runtime Statistics...</h3>
      </div>
    );
  }
}

const getBackgroundColor = (abs_time: number, con_time: number) => {
  if (abs_time > con_time) {
    return "#f08080";
  } else {
    return "#bcf5bc";
  }
};

const SpeedUpTooltip = ({ active, payload }: { active: any; payload: any }) => {
  if (active && payload && payload.length) {
    return (
      <div
        style={{
          background: "white",
          padding: "10px",
          border: "1px solid #ccc",
        }}
      >
        <p>
          <strong>Benchmark:</strong> {payload[0].payload.example}
        </p>
        <p>
          <strong>Abstract:</strong> {payload[0].payload.abs_time} seconds
        </p>
        <p>
          <strong>Concrete:</strong> {payload[0].payload.con_time} seconds
        </p>
      </div>
    );
  }
  return null;
};

function Row({ benchmark, index }: { benchmark: Benchmark; index: number }) {
  const [showInstances, setShowInstances] = useState(false);
  const { art } = Route.useParams();
  const { compare, expand, strategy } = Route.useSearch();
  const compareAgainst = useArtifact(compare);
  const benchResult = getResult(benchmark, strategy);
  const benchmarkSuccess =
    benchResult !== undefined &&
    (("Success" in benchResult &&
      benchResult.Success.used_instances.length !== 0) ||
      ("NoProgress" in benchResult &&
        benchResult.NoProgress.used_instances.length !== 0));

  const compareResult = getResult(
    compareAgainst.data?.benchmarks?.[index],
    strategy,
  );
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
            {isSuccess &&
              (showInstances || expand ? <FaCaretDown /> : <FaCaretRight />)}
          </div>

          {benchmark.example}
        </button>
        <div className="ml-5 flex flex-row items-center gap-1">
          <Link
            to="/artifacts/$art/$problem"
            params={{
              art: art,
              problem: benchmark.example.replaceAll("/", "--"),
            }}
            className="text-sm text-blue-500 hover:text-blue-600 hover:underline dark:text-blue-400 dark:hover:text-blue-500"
          >
            Details
          </Link>

          <Runtime
            benchmark={benchmark}
            compare={compareAgainst?.data?.benchmarks?.[index]}
          />
        </div>
      </td>
      <Status
        result={getResult(benchmark, strategy)}
        showInstances={showInstances || expand}
      />
      {compare !== "" &&
        !!compareAgainst.data &&
        !!compareAgainst.data.benchmarks && (
          <Status
            result={getResult(compareAgainst.data.benchmarks[index], strategy)}
            showInstances={showInstances || expand}
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

  if ("FoundProof" in result) {
    return (
      <td className="m-0 bg-green-200 px-2 text-left align-top dark:bg-green-800">
        Found Proof!
      </td>
    );
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

function Runtime({
  benchmark,
  compare,
}: {
  benchmark: Benchmark;
  compare?: Benchmark;
}) {
  const abstractRuntime = getRuntime(benchmark, "abstract");
  const concreteRuntime = getRuntime(benchmark, "concrete");
  const compareRuntime = getRuntime(compare);

  if (abstractRuntime === undefined || concreteRuntime === undefined) {
    return undefined;
  }

  const diff = concreteRuntime - abstractRuntime;

  if (compareRuntime !== undefined) {
    return <span className="text-sm">compare</span>;
  } else {
    if (diff > 0) {
      return (
        <>
          <span className="text-sm text-green-700 dark:text-green-300">
            +{concreteRuntime - abstractRuntime}ms
          </span>
        </>
      );
    } else {
      return (
        <>
          <span className="text-sm text-red-500">
            {concreteRuntime - abstractRuntime}ms
          </span>
        </>
      );
    }
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
