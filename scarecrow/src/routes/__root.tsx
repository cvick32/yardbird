import {
  Link,
  Outlet,
  createRootRouteWithContext,
  useMatch,
} from "@tanstack/react-router";
import { QueryClient } from "@tanstack/react-query";
import { AuthContext } from "../AuthProvider";
import { FaCrow, FaDoorOpen, FaGithub } from "react-icons/fa6";
import { useArtifact, useArtifacts } from "../fetch";
import { useNavigate } from "@tanstack/react-router";
import { useState } from "react";
import { CommitMessage, CommitRef } from ".";

interface RouterContext {
  queryClient: QueryClient;
  auth: AuthContext;
}

export const Route = createRootRouteWithContext<RouterContext>()({
  component: RootComponent,
});

function RootComponent() {
  return (
    <>
      <div className="sticky top-0 z-20 flex flex-wrap items-center gap-4 border-b border-slate-300 bg-slate-100 p-2 px-4 md:flex-nowrap">
        <div>
          <Link
            to="/"
            className="flex flex-row items-center gap-1 text-lg hover:underline [&.active]:font-bold"
          >
            <FaCrow />
            Artifacts
          </Link>
        </div>
        <Breadcrumbs />
        <div className="grow"></div>
        <div>
          <a
            href="https://github.com/cvick32/yardbird"
            className="flex flex-row items-center gap-1 text-lg hover:underline [&.active]:font-bold"
          >
            <FaGithub />
            Repo
          </a>
        </div>
        <div>
          <Link
            to="/logout"
            className="flex flex-row items-center gap-1 text-lg hover:underline [&.active]:font-bold"
          >
            <FaDoorOpen />
            Log Out
          </Link>
        </div>
      </div>
      <hr />
      <div className="m-2">
        <Outlet />
      </div>
    </>
  );
}

function Breadcrumbs() {
  const artifactMatch = useMatch({
    from: "/artifacts/$art",
    shouldThrow: false,
  });

  const artifact = useArtifact(artifactMatch?.params.art);
  const compareArtifact = useArtifact(artifactMatch?.search.compare);
  const artifacts = useArtifacts();
  const navigate = useNavigate({ from: "/artifacts/$art" });
  const [filterVal, setFilterVal] = useState<string>(
    artifactMatch?.search.filter ?? "",
  );

  if (!artifactMatch || !artifact.data) {
    return undefined;
  }

  return (
    <div className="order-last flex flex-row flex-wrap items-center gap-2 text-sm md:order-none md:flex-nowrap">
      <label htmlFor="compare" className="font-bold">
        Compare:
      </label>
      <select
        name="compare"
        id="compare"
        onChange={(ev) => {
          const compare = ev.target.value.trim();
          const filter =
            compare === "" && filterVal === "differ" ? "" : filterVal;
          setFilterVal(filter);
          navigate({
            search: () => ({
              compare,
              filter,
            }),
          });
        }}
        defaultValue={artifactMatch.search.compare}
      >
        <option value="">None</option>
        {!!artifacts.data &&
          artifacts.data.data.artifacts
            .filter((art: any) => `${art.id}` !== `${artifact.data.id}`)
            .map((art: any, idx: number) => {
              let date = new Date(Date.parse(art.created_at));
              let dayString = date.toLocaleDateString("en-US");
              return (
                <option key={idx} value={art.id}>
                  {dayString} {`#${art.workflow_run.head_sha.slice(0, 7)}`}
                </option>
              );
            })}
      </select>
      <label htmlFor="filter" className="font-bold">
        Filter:
      </label>
      <select
        name="filter"
        id="filter"
        onChange={(ev) => {
          const filter = ev.target.value.trim();
          setFilterVal(filter);
          navigate({
            search: () => ({
              compare: artifactMatch.search.compare,
              filter,
            }),
          });
        }}
        value={filterVal}
      >
        <option value="">None</option>
        <option value="success">Success</option>
        <option value="timeout">Timeout</option>
        <option value="error">Error</option>
        <option value="panic">Panic</option>
        <option value="differ">Differ</option>
      </select>
      <div className="flex flex-row flex-wrap gap-2 md:flex-nowrap">
        <CommitRef sha={artifact.data.commitSha} />
        <CommitMessage sha={artifact.data.commitSha} />
        {!!compareArtifact.data && (
          <div className="flex flex-row gap-2">
            <span>{"->"}</span>
            <CommitRef sha={compareArtifact.data.commitSha} />
            <CommitMessage sha={compareArtifact.data.commitSha} />
          </div>
        )}
      </div>
    </div>
  );
}
