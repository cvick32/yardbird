import {
  Link,
  MatchRoute,
  Outlet,
  createRootRouteWithContext,
  useMatch,
} from "@tanstack/react-router";
import { QueryClient } from "@tanstack/react-query";
import { AuthContext } from "../AuthProvider";
import {
  FaArrowLeft,
  FaCrow,
  FaDoorOpen,
  FaGithub,
  FaUpload,
} from "react-icons/fa6";
import { useArtifact, useArtifacts } from "../fetch";
import { useNavigate } from "@tanstack/react-router";
import { CommitMessage, CommitRef } from ".";
import { useIsLargeScreen } from "../useIsLargeScreen";
import { useFiles } from "../FileProvider";

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
      <div className="sticky top-0 z-[110] border-b border-slate-300 bg-slate-100 px-4 dark:border-slate-700 dark:bg-slate-900 dark:text-white">
        {isLargeScreen ? <LargeHeader /> : <SmallHeader />}
      </div>
      <div className="p-2 dark:bg-slate-800">
        <Outlet />
      </div>
    </>
  );
}

function LargeHeader() {
  return (
    <>
      <div className="flex flex-wrap flex-nowrap items-center gap-4 p-2">
        <div className="flex flex-row items-center gap-2">
          <BackLink />
          <MatchRoute to="/artifacts/$art">
            <ArtifactSettings />
          </MatchRoute>
        </div>
        <div className="grow"></div>
        <UploadLink />
        <RepoLink />
        <LogoutLink />
      </div>
      <MatchRoute to="/artifacts/$art">
        <div className="mb-2 grow">
          <CompareCommits />
        </div>
      </MatchRoute>
    </>
  );
}

function SmallHeader() {
  return (
    <>
      <div className="flex flex-wrap flex-nowrap items-center gap-4 p-2">
        <div className="flex flex-row items-center gap-2">
          <BackLink />
        </div>
        <div className="grow"></div>
        <UploadLink />
        <RepoLink />
        <LogoutLink />
      </div>
      <MatchRoute to="/artifacts/$art">
        <div className="mb-2 flex flex-wrap gap-2">
          <ArtifactSettings />
        </div>
      </MatchRoute>
    </>
  );
}

function ArtifactSettings() {
  return (
    <>
      <CompareSelect />
      <FilterSelect />
      <ExpandToggle />
    </>
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
        className="dark:bg-slate-800"
        onChange={(ev) => {
          const compare = ev.target.value.trim();
          navigate({
            search: (prev) => ({
              ...prev,
              compare,
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
        className="dark:bg-slate-800"
        onChange={(ev) => {
          const filter = ev.target.value.trim();
          navigate({
            search: (prev) => ({
              ...prev,
              filter,
            }),
          });
        }}
        value={artifactMatch.search.filter}
      >
        <option value="">None</option>
        <option value="success">Success</option>
        <option value="no-progress">No Progress</option>
        <option value="trivial">Trivial</option>
        <option value="timeout">Timeout</option>
        <option value="error">Error</option>
        <option value="panic">Panic</option>
        <option value="differ">Differ</option>
      </select>
    </div>
  );
}

function ExpandToggle() {
  const artifactMatch = useMatch({
    from: "/artifacts/$art",
    shouldThrow: false,
  });

  const navigate = useNavigate({ from: "/artifacts/$art" });

  return (
    <div className="flex flex-row items-center gap-2">
      <label htmlFor="expand" className="font-bold">
        Expand:
      </label>
      <input
        type="checkbox"
        checked={artifactMatch?.search.expand}
        onChange={() =>
          navigate({
            search: {
              compare: artifactMatch?.search.compare ?? "",
              filter: artifactMatch?.search.filter ?? "",
              expand: !artifactMatch?.search.expand,
            },
          })
        }
      />
    </div>
  );
}

function BackLink() {
  return (
    <MatchRoute to="/artifacts/$art/$problem">
      {(match) => {
        if (!match) {
          return (
            <Link
              to="/"
              className="flex flex-row items-center gap-1 text-lg hover:underline [&.active]:font-bold"
            >
              <FaCrow />
              Artifacts
            </Link>
          );
        }
        return (
          <div className="flex flex-row items-center gap-10">
            <Link
              to="/artifacts/$art"
              params={{
                art: match.art,
              }}
              search={{
                compare: "",
                filter: "",
                expand: false,
              }}
              className="flex flex-row items-center gap-1 text-lg text-blue-500 hover:text-blue-600 hover:underline dark:text-blue-400 dark:hover:text-blue-500"
            >
              <FaArrowLeft />
              Back
            </Link>
            <div>
              Details for <b>{match.problem.split("--")[1]}</b>
            </div>
          </div>
        );
      }}
    </MatchRoute>
  );
}

function UploadLink() {
  const { addFiles } = useFiles();

  return (
    <div className="tetxt-lg flex flex-row items-center gap-1 hover:underline">
      <FaUpload />
      <label htmlFor="file-upload" className="cursor-pointer">
        Upload
        <input
          type="file"
          id="file-upload"
          className="sr-only"
          accept=".json"
          onChange={(ev) => {
            if (!!ev.target.files) {
              addFiles([...ev.target.files]);
            }
          }}
        />
      </label>
    </div>
  );
}

function RepoLink() {
  return (
    <div>
      <a
        href="https://github.com/cvick32/yardbird"
        className="flex flex-row items-center gap-1 text-lg hover:underline [&.active]:font-bold"
      >
        <FaGithub />
        Repo
      </a>
    </div>
  );
}

function LogoutLink() {
  return (
    <div>
      <Link
        to="/logout"
        className="flex flex-row flex-nowrap items-center gap-1 text-nowrap text-lg hover:underline [&.active]:font-bold"
      >
        <FaDoorOpen />
        Log Out
      </Link>
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
        {artifact.data.commitSha === "" ? (
          <span>{artifact.data.id.substring(6)}</span>
        ) : (
          <>
            <CommitRef sha={artifact.data.commitSha} />
            <CommitMessage sha={artifact.data.commitSha} />
          </>
        )}
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
