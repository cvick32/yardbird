import { createFileRoute, Link, redirect } from "@tanstack/react-router";
import {
  benchmarkSummary,
  useArtifact,
  useArtifacts,
  useCommitMessage,
  useInProgressWorkflows,
} from "../fetch";
import { Fragment, PropsWithChildren, ReactElement, useMemo } from "react";

export const Route = createFileRoute("/")({
  beforeLoad: ({ context }) => {
    if (!context.auth.isAuthenticated) {
      throw redirect({ to: "/oauth" });
    }
  },
  component: Index,
});

function Index() {
  const artifacts = useArtifacts();
  const inProgress = useInProgressWorkflows();

  const table: [string[], (props: { art: any }) => ReactElement][] = useMemo(
    () => [
      [["Date", "Time"], DateCol],
      [
        ["Success", "Trivial", "Timeout", "Error", "Panic", "Total"],
        ({ art }) => <Stats key={`stats-${art.id}`} id={art.id as string} />,
      ],
      [
        ["Results"],
        ({ art }) => (
          <Col key={`results-${art.id}`}>
            <Link
              to="/artifacts/$art"
              params={{
                art: art.id,
              }}
              search={{ compare: "", filter: "" }}
              className="text-blue-500 hover:text-blue-600 hover:underline"
            >
              Results
            </Link>
          </Col>
        ),
      ],
      [
        ["Branch"],
        ({ art }) => (
          <Col key={`branch-${art.id}`}>{art.workflow_run.head_branch}</Col>
        ),
      ],
      [
        ["Commit"],
        ({ art }) => (
          <Col key={`commit-${art.id}`}>
            <CommitRef sha={art.workflow_run.head_sha} />
          </Col>
        ),
      ],
      [
        ["Message"],
        ({ art }) => {
          return (
            <Col key={`message-${art.id}`}>
              <CommitMessage sha={art.workflow_run.head_sha} />
            </Col>
          );
        },
      ],
    ],
    [],
  );

  if (!artifacts.data) {
    return <div>Loading...</div>;
  }

  return (
    <table className="max-w-60">
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
        {!!inProgress.data && (
          <tr className="hover:bg-gray-200" key={"in-progress-workflow"}>
            {inProgress.data.map((workflow: any, idx: number) => (
              <Fragment key={`workflow-${idx}`}>
                <DateCol art={workflow} />
                <Col />
                <Col />
                <Col />
                <Col />
                <Col />
                <Col />
                <Col>
                  <a
                    href={workflow.html_url}
                    className="text-blue-500 hover:text-blue-600 hover:underline"
                  >
                    {workflow.status}
                  </a>
                </Col>
                <Col>{workflow.head_branch}</Col>
                <Col>
                  <CommitRef sha={workflow.head_sha} />
                </Col>
                <Col>
                  <div className="w-80 truncate">{workflow.display_title}</div>
                </Col>
              </Fragment>
            ))}
          </tr>
        )}
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
    <Fragment key={`day-time-${art.id}`}>
      <Col className="whitespace-nowrap">{dayString}</Col>
      <Col className="whitespace-nowrap">{timeString}</Col>
    </Fragment>
  );
}

function Stats({ id }: { id: string }) {
  let stats = useArtifact(id, benchmarkSummary);

  if (stats.data === undefined) {
    return (
      <>
        <Col key={`0-${id}`} />
        <Col key={`1-${id}`} />
        <Col key={`2-${id}`} />
        <Col key={`3-${id}`} />
        <Col key={`4-${id}`} />
        <Col key={`5-${id}`} />
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
      <Col key={`0-${id}`} className="text-green-600">
        {stats.data.success}
      </Col>
      <Col key={`1-${id}`} className="text-teal-600">
        {stats.data.trivialSuccess}
      </Col>
      <Col key={`2-${id}`} className="text-orange-600">
        {stats.data.timeout}
      </Col>
      <Col key={`3-${id}`} className="text-red-600">
        {stats.data.error}
      </Col>
      <Col key={`4-${id}`} className="text-purple-600">
        {stats.data.panic}
      </Col>
      <Col key={`5-${id}`} className="text-purple-600">
        {total}
      </Col>
    </>
  );
}

export function CommitMessage({ sha }: { sha: string }) {
  const query = useCommitMessage(sha);

  if (!query.data) {
    return <div>...</div>;
  }

  return <div className="w-80 truncate">{query.data.data.commit.message}</div>;
}

export function CommitRef({ sha }: { sha: string }) {
  const link = `https://github.com/cvick32/yardbird/commit/${sha}`;
  return (
    <a
      href={link}
      className="text-blue-500 hover:text-blue-600 hover:underline"
    >{`#${sha.slice(0, 7)}`}</a>
  );
}

function Col({
  children,
  className,
}: PropsWithChildren<{ className?: string }>) {
  return (
    <th className={`pr-2 text-left align-top ${className}`}>{children}</th>
  );
}
