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
      {artifacts.data.data.artifacts.map((art: any, idx: number) => (
        <Link
          key={idx}
          to="/artifacts/$art"
          params={{
            art: art.id,
          }}
        >
          <div>
            {art.created_at} {art.id} {art.workflow_run.head_branch}{" "}
            {art.workflow_run.head_sha}
          </div>
        </Link>
      ))}
    </div>
  );
}
