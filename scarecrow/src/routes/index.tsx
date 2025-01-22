import { createFileRoute, Link, redirect } from "@tanstack/react-router";
import {
  Artifact,
  benchmarkSummary,
  selectGeomean,
  useArtifact,
  useArtifacts,
  useCommitMessage,
  useInProgressWorkflows,
} from "../fetch";
import { PropsWithChildren, Children, ReactNode } from "react";
import { GoGitBranch } from "react-icons/go";
import { useFiles } from "../FileProvider";
import { FaPencilAlt } from "react-icons/fa";

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
  const { files, deleteFile } = useFiles();

  console.log(files);

  if (!artifacts.data) {
    return <div>Loading All Artifacts...</div>;
  }

  return (
    <div>
      <div className="sticky top-[45px] z-[100] my-1 flex flex-row flex-wrap gap-x-2 bg-slate-200 p-1 dark:bg-slate-700 dark:text-white">
        <div
          className={[
            "flex w-full flex-grow flex-row gap-2 text-sm",
            "md:w-fit md:grow-0 md:gap-0 md:text-base",
          ].join(" ")}
        >
          <span className="font-bold md:w-[90px]"></span>
          <span className="font-bold md:w-[80px]"></span>
        </div>
        <FlexGrid className="font-bold">
          <>Success</>
          <>No Progress</>
          <>Trivial</>
          <>Failures</>
          <>Total</>
          <>Speedup</>
          <></>
        </FlexGrid>
      </div>
      {[...files.entries()].map(
        ([id, artifact]: [string, Artifact], idx: number) => {
          return (
            <Row
              key={idx}
              stats=<Stats id={id} />
              link=<Link
                to="/artifacts/$art"
                params={{ art: id }}
                search={{ compare: "", filter: "", expand: false }}
                className="text-blue-500 hover:text-blue-600 hover:underline dark:text-blue-400 dark:hover:text-blue-500"
              >
                Results
              </Link>
              branchIcon=<FaPencilAlt
                size="12"
                className="shrink-0 text-black dark:text-white"
              />
              branch={"local"}
              commit=<div className="text-black dark:text-white">
                {artifact.id.substring(6)}
              </div>
              extra=<>
                <div className="grow"></div>
                <div>
                  <button
                    className="rounded-md bg-red-500 px-2 text-white"
                    onClick={() => deleteFile(artifact.id)}
                  >
                    Delete
                  </button>
                </div>
              </>
            />
          );
        },
      )}
      {!!inProgress.data &&
        inProgress.data.map((workflow: any, idx: number) => {
          let date = new Date(Date.parse(workflow.created_at));
          let dayString = date.toLocaleDateString("en-US");
          let timeString = date.toLocaleTimeString("en-US", {
            hour: "2-digit",
            minute: "2-digit",
          });
          return (
            <Row
              key={idx}
              day={dayString}
              time={timeString}
              stats=<FlexGrid className="dark:text-white">
                <div key={`0-${idx}`}>-</div>
                <div key={`1-${idx}`}>-</div>
                <div key={`2-${idx}`}>-</div>
                <div key={`3-${idx}`}>-</div>
                <div key={`4-${idx}`}>-</div>
                <div key={`5-${idx}`}>-</div>
              </FlexGrid>
              link=<WorkflowStatus
                href={workflow.html_url}
                status={workflow.status}
              />
              branch={workflow.head_branch}
              commit=<CommitRef sha={workflow.head_sha} />
              message=<CommitMessage sha={workflow.head_sha} />
            />
          );
        })}
      {artifacts.data.data.artifacts.map((art: any, idx: number) => {
        let date = new Date(Date.parse(art.created_at));
        let dayString = date.toLocaleDateString("en-US");
        let timeString = date.toLocaleTimeString("en-US", {
          hour: "2-digit",
          minute: "2-digit",
        });
        return (
          <Row
            key={idx}
            day={dayString}
            time={timeString}
            stats=<Stats id={art.id} />
            link=<Link
              to="/artifacts/$art"
              params={{ art: art.id }}
              search={{ compare: "", filter: "", expand: false }}
              className="text-blue-500 hover:text-blue-600 hover:underline dark:text-blue-400 dark:hover:text-blue-500"
            >
              Results
            </Link>
            branch={art.workflow_run.head_branch}
            commit=<CommitRef sha={art.workflow_run.head_sha} />
            message=<CommitMessage sha={art.workflow_run.head_sha} />
          />
        );
      })}
    </div>
  );
}

function Row({
  day,
  time,
  stats,
  link,
  branchIcon,
  branch,
  commit,
  message,
  extra,
}: {
  day?: ReactNode;
  time?: ReactNode;
  stats: ReactNode;
  link: ReactNode;
  branchIcon?: ReactNode;
  branch: ReactNode;
  commit: ReactNode;
  message?: ReactNode;
  extra?: ReactNode;
}) {
  return (
    <div className="my-1 flex flex-row flex-wrap gap-x-2 rounded-md border p-1 hover:bg-slate-200 md:flex-nowrap dark:border-slate-700 dark:hover:bg-slate-900">
      <div
        className={[
          "flex w-full flex-grow flex-row gap-2 text-sm",
          "md:w-fit md:grow-0 md:gap-0 md:text-base",
        ].join(" ")}
      >
        <span className="text-slate-500 md:w-[90px] md:text-black dark:md:text-white">
          {day}
        </span>
        <span className="text-slate-500 md:w-[80px] md:text-black dark:md:text-white">
          {time}
        </span>
      </div>
      {stats}
      {link}
      <div className="flex flex-row gap-2 md:gap-0">
        <div className="group flex flex-row items-center gap-1 hover:z-20 hover:overflow-visible md:w-[100px] md:truncate">
          {branchIcon || (
            <GoGitBranch
              size="14"
              className="shrink-0 text-black dark:text-white"
            />
          )}
          <span className="text-black group-hover:bg-slate-200 dark:text-white dark:group-hover:bg-slate-900">
            {branch}
          </span>
        </div>
        <div className="flex flex-row items-center">{commit}</div>
      </div>
      <div className="w-full truncate md:w-fit">{message}</div>
      {extra}
    </div>
  );
}

function FlexGrid({
  children,
  className,
}: PropsWithChildren<{ className?: string }>) {
  return (
    <div className="ml-2 flex w-full flex-grow flex-row md:ml-0 md:w-fit md:grow-0">
      {Children.map(children, (elem, idx) => (
        <div key={idx} className={`w-[80px] truncate ${className ?? ""}`}>
          {elem}
        </div>
      ))}
    </div>
  );
}

function Stats({ id }: { id: string }) {
  let stats = useArtifact(`${id}`, benchmarkSummary);
  let geomean = useArtifact(`${id}`, (artifact) =>
    selectGeomean("success", artifact),
  );

  if (stats.data === undefined) {
    return (
      <FlexGrid className="text-black dark:text-white">
        <div key={`0-${id}`}>-</div>
        <div key={`1-${id}`}>-</div>
        <div key={`2-${id}`}>-</div>
        <div key={`3-${id}`}>-</div>
        <div key={`4-${id}`}>-</div>
        <div key={`5-${id}`}>-</div>
      </FlexGrid>
    );
  }

  const total =
    stats.data.success +
    stats.data.noProgress +
    stats.data.trivialSuccess +
    stats.data.timeout +
    stats.data.error +
    stats.data.panic;

  return (
    <FlexGrid className="text-black dark:text-white">
      <div
        key={`0-${id}`}
        className="font-bold text-green-600 dark:text-green-500"
      >
        {stats.data.success}
      </div>
      <div
        key={`1-${id}`}
        className="font-bold text-pink-600 dark:text-pink-500"
      >
        {stats.data.noProgress}
      </div>

      <div
        key={`2-${id}`}
        className="font-bold text-teal-600 dark:text-teal-500"
      >
        {stats.data.trivialSuccess}
      </div>
      <div key={`3-${id}`} className="flex flex-row gap-[2px] font-bold">
        <span className="text-orange-600 dark:text-orange-500">
          {stats.data.timeout}
        </span>
        /
        <span className="text-red-600 dark:text-red-500">
          {stats.data.error}
        </span>
        /
        <span className="text-purple-600 dark:text-purple-500">
          {stats.data.panic}
        </span>
      </div>
      <div key={`6-${id}`} className="font-bold text-black dark:text-gray-300">
        {total}
      </div>
      {geomean.data && (
        <div
          className={
            geomean.data > 1.0
              ? "text-green-700 dark:text-green-300"
              : "text-red-500"
          }
        >
          {geomean.data.toFixed(2)}×
        </div>
      )}
    </FlexGrid>
  );
}

export function CommitMessage({ sha }: { sha: string }) {
  const query = useCommitMessage(sha);

  if (!query.data) {
    return <div>...</div>;
  }

  return <RawCommitMessage message={query.data.data.commit.message} />;
}

function RawCommitMessage({ message }: { message: string }) {
  if (message.includes("\n")) {
    message = message.split("\n")[0];
  }
  const tagPattern = /\[.*\]/;
  const tag = message.match(tagPattern);
  message = message.replace(tagPattern, "");

  return (
    <div className="truncate text-black dark:text-white">
      <span className="font-mono text-sm">{tag}</span>
      {message}
    </div>
  );
}

export function CommitRef({ sha }: { sha: string }) {
  const link = `https://github.com/cvick32/yardbird/commit/${sha}`;
  return (
    <a
      href={link}
      className="text-blue-500 hover:text-blue-600 hover:underline dark:text-blue-400 dark:hover:text-blue-500"
    >{`#${sha.slice(0, 7)}`}</a>
  );
}

function WorkflowStatus({ status, href }: { status: string; href: string }) {
  // Can be one of: completed, action_required, cancelled, failure, neutral, skipped, stale, success, timed_out, in_progress, queued, requested, waiting, pending

  let message = status;
  let spinner = undefined;
  if (status === "completed") {
    message = "done";
  } else if (status === "in_progress") {
    message = "wip";
    spinner = (
      <span className="relative flex h-2 w-2">
        <span className="absolute inline-flex h-full w-full animate-ping rounded-full bg-blue-500 opacity-75"></span>
        <span className="relative inline-flex h-2 w-2 rounded-full bg-blue-500"></span>
      </span>
    );
  }

  return (
    <a
      href={href}
      className="flex w-[54.45px] flex-row items-center gap-2 text-blue-500 hover:text-blue-600 hover:underline dark:text-blue-400 dark:hover:text-blue-500"
    >
      {spinner}
      {message}
    </a>
  );
}
