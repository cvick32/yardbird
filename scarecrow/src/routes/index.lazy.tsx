import { createLazyFileRoute, Link } from "@tanstack/react-router";
import { useArtifacts } from "../fetch";

export const Route = createLazyFileRoute("/")({
  component: Index,
});

function Index() {
  const artifacts = useArtifacts();

  if (!artifacts.data) {
    return <div>Loading</div>;
  }

  console.log(artifacts.data);

  return (
    <div className="p-2">
      {artifacts.data.data.artifacts.map((art: any, idx: number) => {
        let date = new Date(Date.parse(art.created_at));
        let dayString = date.toLocaleDateString("en-US");
        let timeString = date.toLocaleTimeString("en-US");
        return (
          <Link
            key={idx}
            to="/artifacts/$art"
            params={{
              art: art.id,
            }}
          >
            <div>
              {dayString} {timeString} {art.workflow_run.head_branch}{" "}
              {art.workflow_run.head_sha.slice(0, 7)}
            </div>
          </Link>
        );
      })}
    </div>
  );
}
