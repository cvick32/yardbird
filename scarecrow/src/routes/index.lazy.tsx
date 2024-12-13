import { createLazyFileRoute, Link } from "@tanstack/react-router";
import { benchmarkSummary, useArtifact, useArtifacts } from "../fetch";
import { PropsWithChildren, ReactElement, useMemo } from "react";

export const Route = createLazyFileRoute("/")({
  component: Index,
});

function githubLink(sha: string) {
  return `https://github.com/cvick32/yardbird/commit/${sha}`;
}

function Index() {
  const artifacts = useArtifacts();

  const table: [string[], (props: { art: any }) => ReactElement][] = useMemo(
    () => [
      [["Date", "Time"], DateCol],
      [
        ["Success", "Trivial", "Timeout", "Error", "Panic", "Total"],
        ({ art }) => <Stats key={"stats"} id={art.id as string} />,
      ],
      [
        ["Results"],
        ({ art }) => (
          <Col key={"results"}>
            <Link
              to="/artifacts/$art"
              params={{
                art: art.id,
              }}
              className="text-blue-500 hover:text-blue-600 hover:underline"
            >
              Results
            </Link>
          </Col>
        ),
      ],
      [
        ["Branch"],
        ({ art }) => <Col key="branch">{art.workflow_run.head_branch}</Col>,
      ],
      [
        ["Commit"],
        ({ art }) => (
          <Col key={"commit"}>
            <button
              className="text-blue-500 hover:text-blue-600 hover:underline"
              onClick={(e) => {
                e.preventDefault();
                window.location.href = githubLink(art.workflow_run.head_sha);
              }}
            >{`#${art.workflow_run.head_sha.slice(0, 7)}`}</button>
          </Col>
        ),
      ],
    ],
    [],
  );

  if (!artifacts.data) {
    return <div>Loading</div>;
  }

  return (
    <table>
      <thead>
        <tr>
          {table
            .map(([h, _]) => h)
            .flat()
            .map((h) => (
              <Col key={h} className="font-bold">
                {h}
              </Col>
            ))}
        </tr>
      </thead>
      <tbody>
        {artifacts.data.data.artifacts.map((art: any, idx: number) => (
          <tr className="hover:bg-gray-200" key={idx}>
            {table.map(([_, elem]) => elem({ art }))}
          </tr>
        ))}
      </tbody>
    </table>
  );
}

function DateCol({ art }: { art: any }) {
  let date = new Date(Date.parse(art.created_at));
  let dayString = date.toLocaleDateString("en-US");
  let timeString = date.toLocaleTimeString("en-US");

  return (
    <>
      <Col key={"day"}>{dayString}</Col>
      <Col key={"time"}>{timeString}</Col>
    </>
  );
}

function Stats({ id }: { id: string }) {
  let stats = useArtifact(id, benchmarkSummary);

  if (stats.data === undefined) {
    return (
      <>
        <Col key={0} />
        <Col key={1} />
        <Col key={2} />
        <Col key={3} />
        <Col key={4} />
        <Col key={5} />
      </>
    );
  }

  const total =
    stats.data.success +
    stats.data.trivialSuccess +
    stats.data.timeout +
    stats.data.error +
    stats.data.panic;

  return (
    <>
      <Col key={0} className="text-green-600">
        {stats.data.success}
      </Col>
      <Col key={1} className="text-teal-600">
        {stats.data.trivialSuccess}
      </Col>
      <Col key={2} className="text-orange-600">
        {stats.data.timeout}
      </Col>
      <Col key={3} className="text-red-600">
        {stats.data.error}
      </Col>
      <Col key={4} className="text-purple-600">
        {stats.data.panic}
      </Col>
      <Col key={5} className="text-purple-600">
        {total}
      </Col>
    </>
  );
}

function Col({
  children,
  className,
}: PropsWithChildren<{ className?: string }>) {
  return (
    <th className={`text-left align-top pr-2 ${className}`}>{children}</th>
  );
}
