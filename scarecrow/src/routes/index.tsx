import { createFileRoute, Link, redirect } from "@tanstack/react-router";
import {
  Artifact,
  benchmarkSummary,
  useArtifact,
  useArtifacts,
  useCommitMessage,
  useInProgressWorkflows,
} from "../fetch";
import { PropsWithChildren, Children } from "react";
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
        <FlexGrid className="w-[75px] font-bold">
          <>Success</>
          <>No Progress</>
          <>Trivial</>
          <>Timeout</>
          <>Error</>
          <>Panic</>
          <>Total</>
          <></>
        </FlexGrid>
      </div>
      {[...files.entries()].map(
        ([id, artifact]: [string, Artifact], idx: number) => {
          return (
            <div
              className="my-1 flex flex-row flex-wrap gap-x-2 rounded-md border p-1 hover:bg-slate-200 md:flex-nowrap dark:border-slate-700 dark:hover:bg-slate-900"
              key={idx}
            >
              <div
                className={[
                  "flex w-full flex-grow flex-row gap-2 text-sm",
                  "md:w-fit md:grow-0 md:gap-0 md:text-base",
                ].join(" ")}
              >
                <span className="text-slate-500 md:w-[90px] md:text-black"></span>
                <span className="text-slate-500 md:w-[80px] md:text-black"></span>
              </div>
              <Stats id={id} className="w-[75px]" />
              <Link
                to="/artifacts/$art"
                params={{ art: id }}
                search={{ compare: "", filter: "", expand: false }}
                className="text-blue-500 hover:text-blue-600 hover:underline dark:text-blue-400 dark:hover:text-blue-500"
              >
                Results
              </Link>
              <div className="flex flex-row gap-2 md:gap-0">
                <div className="group flex flex-row items-center gap-1 hover:z-20 hover:overflow-visible md:w-[100px] md:truncate">
                  <FaPencilAlt
                    size="12"
                    className="shrink-0 text-black dark:text-white"
                  />
                  <span className="text-black group-hover:bg-slate-200 dark:text-white dark:group-hover:bg-slate-900">
                    local
                  </span>
                </div>
                <div className="text-black dark:text-white">
                  {artifact.id.substring(6)}
                </div>
              </div>
              <div className="grow"></div>
              <div>
                <button
                  className="rounded-md bg-red-500 px-2 text-white"
                  onClick={() => deleteFile(artifact.id)}
                >
                  Delete
                </button>
              </div>
            </div>
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
            <div
              className="my-1 flex flex-row flex-wrap gap-x-2 rounded-md border p-1 hover:bg-slate-200 md:flex-nowrap dark:border-slate-700 dark:hover:bg-slate-900"
              key={idx}
            >
              <div
                className={[
                  "flex w-full flex-grow flex-row gap-2 text-sm",
                  "md:w-fit md:grow-0 md:gap-0 md:text-base",
                ].join(" ")}
              >
                <span className="text-slate-500 md:w-[90px] md:text-black dark:md:text-white">
                  {dayString}
                </span>
                <span className="text-slate-500 md:w-[80px] md:text-black dark:md:text-white">
                  {timeString}
                </span>
              </div>
              <FlexGrid className="w-[75px] dark:text-white">
                <div key={`0-${idx}`}>-</div>
                <div key={`1-${idx}`}>-</div>
                <div key={`2-${idx}`}>-</div>
                <div key={`3-${idx}`}>-</div>
                <div key={`4-${idx}`}>-</div>
                <div key={`5-${idx}`}>-</div>
                <div key={`6-${idx}`}>-</div>
              </FlexGrid>
              <WorkflowStatus
                href={workflow.html_url}
                status={workflow.status}
              />
              <div className="flex flex-row gap-2 md:gap-0">
                <div className="group flex flex-row items-center gap-1 hover:z-20 hover:overflow-visible md:w-[100px] md:truncate">
                  <GoGitBranch
                    size="14"
                    className="shrink-0 text-black dark:text-white"
                  />
                  <span className="text-black group-hover:bg-slate-200 dark:text-white dark:group-hover:bg-slate-900">
                    {workflow.head_branch}
                  </span>
                </div>
                <div className="flex flex-row items-center text-black dark:text-white">
                  <CommitRef sha={workflow.head_sha} />
                </div>
              </div>
              <div className="w-full truncate md:w-fit">
                <RawCommitMessage message={workflow.display_title} />
              </div>
            </div>
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
          <div
            className="my-1 flex flex-row flex-wrap gap-x-2 rounded-md border p-1 hover:bg-slate-200 md:flex-nowrap dark:border-slate-700 dark:hover:bg-slate-900"
            key={idx}
          >
            <div
              className={[
                "flex w-full flex-grow flex-row gap-2 text-sm",
                "md:w-fit md:grow-0 md:gap-0 md:text-base",
              ].join(" ")}
            >
              <span className="text-slate-500 md:w-[90px] md:text-black dark:md:text-white">
                {dayString}
              </span>
              <span className="text-slate-500 md:w-[80px] md:text-black dark:md:text-white">
                {timeString}
              </span>
            </div>
            <Stats
              id={art.id}
              className="w-[75px] text-black dark:text-white"
            />
            <Link
              to="/artifacts/$art"
              params={{ art: art.id }}
              search={{ compare: "", filter: "", expand: false }}
              className="text-blue-500 hover:text-blue-600 hover:underline dark:text-blue-400 dark:hover:text-blue-500"
            >
              Results
            </Link>
            <div className="flex flex-row gap-2 md:gap-0">
              <div className="group flex flex-row items-center gap-1 hover:z-20 hover:overflow-visible md:w-[100px] md:truncate">
                <GoGitBranch
                  size="14"
                  className="shrink-0 text-black dark:text-white"
                />
                <span className="text-black group-hover:bg-slate-200 dark:text-white dark:group-hover:bg-slate-900">
                  {art.workflow_run.head_branch}
                </span>
              </div>
              <div className="flex flex-row items-center">
                <CommitRef sha={art.workflow_run.head_sha} />
              </div>
            </div>
            <div className="w-full truncate md:w-fit">
              <CommitMessage sha={art.workflow_run.head_sha} />
            </div>
          </div>
        );
      })}
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
        <div key={idx} className={`truncate ${className ?? ""}`}>
          {elem}
        </div>
      ))}
    </div>
  );
}

function Stats({ id, className }: { id: string; className?: string }) {
  let stats = useArtifact(`${id}`, benchmarkSummary);

  if (stats.data === undefined) {
    return (
      <FlexGrid className={className}>
        <div key={`0-${id}`}>-</div>
        <div key={`1-${id}`}>-</div>
        <div key={`2-${id}`}>-</div>
        <div key={`3-${id}`}>-</div>
        <div key={`4-${id}`}>-</div>
        <div key={`5-${id}`}>-</div>
        <div key={`6-${id}`}>-</div>
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
    <FlexGrid className={className}>
      <div
        key={`0-${id}`}
        className={`font-bold text-green-600 dark:text-green-500`}
      >
        {stats.data.success}
      </div>
      <div
        key={`1-${id}`}
        className={`font-bold text-pink-600 dark:text-pink-500`}
      >
        {stats.data.noProgress}
      </div>

      <div
        key={`2-${id}`}
        className={`font-bold text-teal-600 dark:text-teal-500`}
      >
        {stats.data.trivialSuccess}
      </div>
      <div
        key={`3-${id}`}
        className={`font-bold text-orange-600 dark:text-orange-500`}
      >
        {stats.data.timeout}
      </div>
      <div
        key={`4-${id}`}
        className={`font-bold text-red-600 dark:text-red-500`}
      >
        {stats.data.error}
      </div>
      <div
        key={`5-${id}`}
        className={`font-bold text-purple-600 dark:text-purple-500`}
      >
        {stats.data.panic}
      </div>
      <div key={`6-${id}`} className="font-bold text-black dark:text-gray-300">
        {total}
      </div>
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
