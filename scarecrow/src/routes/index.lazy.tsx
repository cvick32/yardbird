import { createLazyFileRoute, Link } from "@tanstack/react-router";
import { benchmarkSummary, useArtifact, useArtifacts } from "../fetch";

export const Route = createLazyFileRoute("/")({
  component: Index,
});

function githubLink(sha: string) {
  return `https://github.com/cvick32/yardbird/commit/${sha}`;
}

function Index() {
  const artifacts = useArtifacts();

  if (!artifacts.data) {
    return <div>Loading</div>;
  }

  return (
    <div className="p-2">
      <div>Order for numbers: Success, Trivial, Timeout, Error, Panic</div>
      {artifacts.data.data.artifacts.map((art: any, idx: number) => (
        <Row art={art} key={idx} />
      ))}
    </div>
  );
}

function Row({ art }: { art: any }) {
  let date = new Date(Date.parse(art.created_at));
  let dayString = date.toLocaleDateString("en-US");
  let timeString = date.toLocaleTimeString("en-US");
  return (
    <Link
      to="/artifacts/$art"
      params={{
        art: art.id,
      }}
    >
      <div className="flex gap-2 hover:bg-gray-200">
        <Stats id={art.id as string} />
        <span>{dayString}</span>
        <span>{timeString}</span>
        <span>branch:{art.workflow_run.head_branch}</span>
        <button
          className="text-blue-500 hover:text-blue-600 hover:underline"
          onClick={(e) => {
            e.preventDefault();
            window.location.href = githubLink(art.workflow_run.head_sha);
          }}
        >{`#${art.workflow_run.head_sha.slice(0, 7)}`}</button>
      </div>
    </Link>
  );
}

function Stats({ id }: { id: string }) {
  let stats = useArtifact(id, benchmarkSummary);

  if (stats.data === undefined) {
    return <div>- - - - -</div>;
  }

  return (
    <div className="flex gap-1">
      <span title="Success" className="text-green-600">
        {stats.data.success}
      </span>
      <span title="Trivial Success" className="text-teal-600">
        {stats.data.trivialSuccess}
      </span>
      <span title="Timeout" className="text-orange-600">
        {stats.data.timeout}
      </span>
      <span title="Error" className="text-red-600">
        {stats.data.error}
      </span>
      <span title="Panic" className="text-pruple-600">
        {stats.data.panic}
      </span>
    </div>
  );
}
