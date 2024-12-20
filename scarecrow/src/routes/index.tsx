import { createFileRoute, Link, redirect } from "@tanstack/react-router";
import {
  benchmarkSummary,
  useArtifact,
  useArtifacts,
  useCommitMessage,
  // useInProgressWorkflows,
} from "../fetch";
import { PropsWithChildren, Children } from "react";

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
  // const inProgress = useInProgressWorkflows();

  if (!artifacts.data) {
    return <div>Loading...</div>;
  }

  return (
    <div>
      <div className="sticky top-[45px] my-1 flex flex-row flex-wrap gap-x-2 bg-slate-200 p-1">
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
          <>Trivial</>
          <>Timeout</>
          <>Error</>
          <>Panic</>
          <>Total</>
          <></>
        </FlexGrid>
      </div>
      {artifacts.data.data.artifacts.map((art: any, idx: number) => {
        let date = new Date(Date.parse(art.created_at));
        let dayString = date.toLocaleDateString("en-US");
        let timeString = date.toLocaleTimeString("en-US", {
          hour: "2-digit",
          minute: "2-digit",
        });
        return (
          <div
            className="my-1 flex flex-row flex-wrap gap-x-2 rounded-md border p-1 hover:bg-slate-200 md:flex-nowrap"
            key={idx}
          >
            <div
              className={[
                "flex w-full flex-grow flex-row gap-2 text-sm",
                "md:w-fit md:grow-0 md:gap-0 md:text-base",
              ].join(" ")}
            >
              <span className="text-slate-500 md:w-[90px] md:text-black">
                {dayString}
              </span>
              <span className="text-slate-500 md:w-[80px] md:text-black">
                {timeString}
              </span>
            </div>
            <Stats id={art.id} className="min-w-[75px]" />
            <div className="flex flex-row gap-2 md:gap-0">
              <div className="group hover:z-20 hover:overflow-visible md:w-[100px] md:truncate">
                <span className="group-hover:bg-slate-200">
                  {art.workflow_run.head_branch}
                </span>
              </div>
              <div className="w-[80px]">
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
        <div key={`6-${id}`}>Results</div>
      </FlexGrid>
    );
  }

  const total =
    stats.data.success +
    stats.data.trivialSuccess +
    stats.data.timeout +
    stats.data.error +
    stats.data.panic;

  return (
    <FlexGrid className={className}>
      <div key={`0-${id}`} className={`text-green-600`}>
        {stats.data.success}
      </div>
      <div key={`1-${id}`} className={`text-teal-600`}>
        {stats.data.trivialSuccess}
      </div>
      <div key={`2-${id}`} className={`text-orange-600`}>
        {stats.data.timeout}
      </div>
      <div key={`3-${id}`} className={`text-red-600`}>
        {stats.data.error}
      </div>
      <div key={`4-${id}`} className={`text-purple-600`}>
        {stats.data.panic}
      </div>
      <div key={`5-${id}`} className={``}>
        {total}
      </div>
      <Link
        to="/artifacts/$art"
        params={{ art: id }}
        search={{ compare: "", filter: "" }}
        className="text-blue-500 hover:text-blue-600 hover:underline"
      >
        Results
      </Link>
    </FlexGrid>
  );
}

export function CommitMessage({ sha }: { sha: string }) {
  const query = useCommitMessage(sha);

  if (!query.data) {
    return <div>...</div>;
  }

  return <div className="truncate">{query.data.data.commit.message}</div>;
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
