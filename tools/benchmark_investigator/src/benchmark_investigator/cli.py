"""CLI entry point; all experiment commands use validated argv, never a shell."""

import argparse
import asyncio
import json
import logging
import sys
import uuid
from pathlib import Path

from .agent import MockBackend, run_campaign
from .artifacts import contained, read_json, sha256, write_json
from .campaign import Campaign, create_campaign, source_manifest
from .codex_backend import CodexCLIBackend
from .findings import render_synthesis
from .models import CampaignConfig, ExperimentConfig, Filters, RunAction
from .profile_query import query_profile
from .runner import execute_run
from .summarizer import summarize_run


def parser():
    root = Path(__file__).resolve().parents[4]
    p = argparse.ArgumentParser(
        prog="investigator", description="Pinned Yardbird benchmark investigations"
    )
    sub = p.add_subparsers(dest="command", required=True)
    init = sub.add_parser("init", help="Build once and pin a new campaign")
    init.add_argument("config", type=Path)
    init.add_argument("--output", type=Path, required=True)
    init.add_argument("--source-root", type=Path, default=root)
    init.add_argument("--binary", type=Path, help="Use a prebuilt binary instead of building")
    run = sub.add_parser("run", help="Run one standalone experiment")
    run.add_argument("benchmark")
    run.add_argument("config", type=Path)
    run.add_argument("--output", type=Path, required=True)
    run.add_argument("--source-root", type=Path, default=root)
    run.add_argument("--binary", type=Path, default=root / "target/release/yardbird")
    run.add_argument("--depth", type=int, default=20)
    run.add_argument("--timeout", type=int, default=300)
    run.add_argument("--kill-grace", type=int, default=10)
    run.add_argument("--ranker-model", type=Path)
    campaign = sub.add_parser("campaign", help="Run/resume logical agents or mandatory baselines")
    campaign.add_argument("directory", type=Path)
    campaign.add_argument("--backend", choices=["codex", "mock"], default="codex")
    campaign.add_argument("--baselines-only", action="store_true")
    campaign.add_argument("--benchmark", action="append", help="Benchmark ID from status")
    experiment = sub.add_parser("experiment", help="Submit one validated adaptive RUN manually")
    experiment.add_argument("directory", type=Path)
    experiment.add_argument("benchmark_id")
    experiment.add_argument("action", type=Path)
    status = sub.add_parser("status")
    status.add_argument("directory", type=Path)
    summarize = sub.add_parser("summarize", help="Regenerate deterministic derived summaries")
    summarize.add_argument("run_directory", type=Path)
    query = sub.add_parser("query", help="Read a bounded profile slice")
    query.add_argument("run_directory", type=Path)
    query.add_argument(
        "view",
        choices=[
            "overview",
            "depth",
            "refinement",
            "timing",
            "rules",
            "quantifiers",
            "egraph",
            "solver",
            "events",
        ],
    )
    query.add_argument("--depth", type=int)
    query.add_argument("--refinement-step", type=int)
    query.add_argument("--rule")
    synthesis = sub.add_parser("synthesize", help="Synthesize all completed findings using Codex")
    synthesis.add_argument("directory", type=Path)
    return p


def backend(campaign):
    c = campaign.config
    return CodexCLIBackend(c.model, c.reasoning_effort, c.agent_timeout_secs)


async def dispatch(args):
    if args.command == "init":
        config = CampaignConfig.model_validate(read_json(args.config))
        campaign = create_campaign(args.source_root, args.output, config, args.binary)
        print(f"Created {campaign.directory}; {len(campaign.benchmarks)} benchmarks")
    elif args.command == "run":
        if not 1 <= args.depth <= 65535 or args.timeout < 0 or args.kill_grace < 1:
            raise ValueError("Invalid depth/timeout/grace")
        config = ExperimentConfig.model_validate(read_json(args.config))
        root, binary = args.source_root.resolve(), args.binary.resolve()
        benchmark = contained(root, args.benchmark)
        if benchmark.suffix != ".vmt":
            raise ValueError("The investigator currently supports VMT inputs only")
        sources = source_manifest(root)
        await execute_run(
            directory=args.output.resolve(),
            run_id=args.output.name,
            benchmark_id=benchmark.stem,
            ordinal=1,
            binary=binary,
            binary_hash=sha256(binary),
            benchmark=benchmark,
            benchmark_hash=sha256(benchmark),
            source_root=root,
            config=config,
            depth=args.depth,
            timeout_secs=args.timeout,
            kill_grace_secs=args.kill_grace,
            ranker=args.ranker_model.resolve() if args.ranker_model else None,
        )
        write_json(
            args.output / "source-manifest.json",
            {"source_root": str(root), "source_files": sources},
        )
        summary = summarize_run(args.output)
        print(json.dumps(summary["outcome"]))
    elif args.command == "summarize":
        summarize_run(args.run_directory)
        print(args.run_directory / "summary.md")
    elif args.command == "query":
        d = args.run_directory
        result = query_profile(
            read_json(d / "profile.json"),
            read_json(d / "summary.json"),
            args.view,
            Filters(depth=args.depth, refinement_step=args.refinement_step, rule=args.rule),
        )
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        campaign = Campaign(args.directory)
        if args.command == "status":
            with campaign.db() as db:
                print(
                    json.dumps(
                        [
                            dict(r)
                            for r in db.execute(
                                """SELECT b.*,COUNT(r.run_id) AS executions FROM benchmarks b LEFT JOIN runs r USING(benchmark_id) GROUP BY b.benchmark_id ORDER BY b.benchmark_id"""
                            )
                        ],
                        indent=2,
                    )
                )
            return
        with campaign.lock():
            if args.command == "campaign":
                await run_campaign(
                    campaign,
                    MockBackend()
                    if args.backend == "mock" or args.baselines_only
                    else backend(campaign),
                    args.baselines_only,
                    args.benchmark,
                )
            elif args.command == "experiment":
                result = await campaign.run(
                    args.benchmark_id, RunAction.model_validate(read_json(args.action))
                )
                print(result["run_id"])
            elif args.command == "synthesize":
                reports = {}
                for bid in campaign.benchmarks:
                    path = campaign.directory / "FINDINGS" / f"FINDINGS-{bid}.md"
                    if not path.exists():
                        raise ValueError(f"Missing findings for {bid}")
                    text = path.read_text()
                    if "MOCK BACKEND" in text:
                        raise ValueError("Mock findings cannot be used for research synthesis")
                    reports[bid] = text
                if (campaign.directory / "SYNTHESIS.md").exists():
                    raise ValueError("SYNTHESIS.md already exists")
                result = await backend(campaign).synthesize(
                    reports, campaign.directory / "synthesis-turns" / uuid.uuid4().hex
                )
                (campaign.directory / "SYNTHESIS.md").write_text(render_synthesis(result))


def main():
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    try:
        asyncio.run(dispatch(parser().parse_args()))
    except (ValueError, RuntimeError, OSError) as exc:
        print(f"investigator: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
    except KeyboardInterrupt:
        print(
            "Interrupted; artifacts remain on disk. Inspect unfinished attempts before resuming.",
            file=sys.stderr,
        )
        raise SystemExit(130) from None


if __name__ == "__main__":
    main()
