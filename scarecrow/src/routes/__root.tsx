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
import { useIsLargeScreen } from "../useIsLargeScreen";

interface RouterContext {
  queryClient: QueryClient;
  auth: AuthContext;
}

export const Route = createRootRouteWithContext<RouterContext>()({
  component: RootComponent,
});

function RootComponent() {
  // render a different header based on screen width
  const isLargeScreen = useIsLargeScreen();

  return (
    <>
      {isLargeScreen ? <LargeHeader /> : <SmallHeader />}
      <div className="m-2">
        <Outlet />
      </div>
    </>
  );
}

function LargeHeader() {
  return (
    <div className="sticky top-0 z-20 h-[75px] border-b border-slate-300 bg-slate-100 p-2 px-4">
      <div className="mb-2 flex flex-wrap flex-nowrap items-center gap-4">
        <div className="flex flex-row items-center gap-2">
          <Link
            to="/"
            className="flex flex-row items-center gap-1 text-lg hover:underline [&.active]:font-bold"
          >
            <FaCrow />
            Artifacts
          </Link>
          <CompareSelect />
          <FilterSelect />
        </div>
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
            className="flex flex-row flex-nowrap items-center gap-1 text-nowrap text-lg hover:underline [&.active]:font-bold"
          >
            <FaDoorOpen />
            Log Out
          </Link>
        </div>
      </div>
      <div className="grow">
        <CompareCommits />
      </div>
    </div>
  );
}

function SmallHeader() {
  return (
    <div className="sticky top-0 z-20 border-b border-slate-300 bg-slate-100 p-2 px-4">
      <div className="mb-2 flex flex-wrap flex-nowrap items-center gap-4">
        <div className="flex flex-row items-center gap-2">
          <Link
            to="/"
            className="flex flex-row items-center gap-1 text-lg hover:underline [&.active]:font-bold"
          >
            <FaCrow />
            Artifacts
          </Link>
        </div>
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
            className="flex flex-row flex-nowrap items-center gap-1 text-nowrap text-lg hover:underline [&.active]:font-bold"
          >
            <FaDoorOpen />
            Log Out
          </Link>
        </div>
      </div>
      <div className="flex flex-wrap gap-2">
        <CompareSelect />
        <FilterSelect />
      </div>
    </div>
  );
}

function CompareSelect() {
  const artifactMatch = useMatch({
    from: "/artifacts/$art",
    shouldThrow: false,
  });

  const artifact = useArtifact(artifactMatch?.params.art);
  const artifacts = useArtifacts();
  const navigate = useNavigate({ from: "/artifacts/$art" });
  const [filterVal, setFilterVal] = useState<string>(
    artifactMatch?.search.filter ?? "",
  );

  if (artifactMatch === undefined || !artifact.data) {
    return undefined;
  }

  return (
    <div className="flex flex-row flex-nowrap gap-2">
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
    </div>
  );
}

function FilterSelect() {
  const artifactMatch = useMatch({
    from: "/artifacts/$art",
    shouldThrow: false,
  });

  const artifact = useArtifact(artifactMatch?.params.art);
  const navigate = useNavigate({ from: "/artifacts/$art" });
  const [filterVal, setFilterVal] = useState<string>(
    artifactMatch?.search.filter ?? "",
  );

  if (!artifactMatch || !artifact.data) {
    return undefined;
  }

  return (
    <div className="flex flex-row flex-nowrap gap-2">
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
        <option value="trivial">Trivial</option>
        <option value="timeout">Timeout</option>
        <option value="error">Error</option>
        <option value="panic">Panic</option>
        <option value="differ">Differ</option>
      </select>
    </div>
  );
}

function CompareCommits() {
  const artifactMatch = useMatch({
    from: "/artifacts/$art",
    shouldThrow: false,
  });

  const artifact = useArtifact(artifactMatch?.params.art);
  const compareArtifact = useArtifact(artifactMatch?.search.compare);

  if (!artifactMatch || !artifact.data) {
    return undefined;
  }

  return (
    <div className="flex flex-row items-center gap-2 text-sm">
      <span className="flex flex-row gap-2 truncate">
        <CommitRef sha={artifact.data.commitSha} />
        <CommitMessage sha={artifact.data.commitSha} />
      </span>
      {!!compareArtifact.data && (
        <>
          <span>{"->"}</span>
          <div className="flex flex-row gap-2 truncate">
            <CommitRef sha={compareArtifact.data.commitSha} />
            <CommitMessage sha={compareArtifact.data.commitSha} />
          </div>
        </>
      )}
    </div>
  );
}
