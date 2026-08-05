#!/usr/bin/env python3
"""Replay, time, and compare a Yardbird capture with a matched Z3 pair."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from z3_profile import (
    ReplayError,
    compare_capture,
    load_builder_manifest,
    replay_build_pair,
    time_stock_replay,
    write_timing_report,
    write_comparison_report,
)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subcommands = parser.add_subparsers(dest="command", required=True)
    replay = subcommands.add_parser(
        "replay", help="replay one capture through stock and instrumented Z3"
    )
    replay.add_argument("--capture-dir", required=True, type=Path)
    replay.add_argument(
        "--z3-build-dir",
        type=Path,
        help="existing z3-builder output; otherwise read its JSON from stdin",
    )
    replay.add_argument("--timeout", type=float, default=60.0)

    timing = subcommands.add_parser(
        "time", help="measure repeated persistent replays through stock Z3"
    )
    timing.add_argument("--capture-dir", required=True, type=Path)
    timing.add_argument(
        "--z3-build-dir",
        type=Path,
        help="existing z3-builder output; otherwise read its JSON from stdin",
    )
    timing.add_argument("--warmups", type=int, default=3)
    timing.add_argument("--repetitions", type=int, default=15)
    timing.add_argument("--timeout", type=float, default=60.0)
    timing.add_argument("--output", type=Path)

    comparison = subcommands.add_parser(
        "compare", help="join stock timing with instrumented array summaries"
    )
    comparison.add_argument("--capture-dir", required=True, type=Path)
    comparison.add_argument(
        "--z3-build-dir",
        type=Path,
        help="existing z3-builder output; otherwise read its JSON from stdin",
    )
    comparison.add_argument("--warmups", type=int, default=3)
    comparison.add_argument("--repetitions", type=int, default=15)
    comparison.add_argument("--timeout", type=float, default=60.0)
    comparison.add_argument("--output", type=Path)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        builder_manifest = _builder_manifest(args.z3_build_dir)
        if args.command == "replay":
            replay = replay_build_pair(
                args.capture_dir,
                builder_manifest,
                timeout_seconds=args.timeout,
            )
        elif args.command == "time":
            report = time_stock_replay(
                args.capture_dir,
                builder_manifest,
                warmups=args.warmups,
                repetitions=args.repetitions,
                timeout_seconds=args.timeout,
            )
        elif args.command == "compare":
            report = compare_capture(
                args.capture_dir,
                builder_manifest,
                warmups=args.warmups,
                repetitions=args.repetitions,
                timeout_seconds=args.timeout,
            )
        else:
            raise AssertionError(f"unhandled command {args.command}")
    except (ReplayError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1

    if args.command == "replay":
        print(f"expected:     {' '.join(replay.expected)}")
        print(f"stock:        {' '.join(replay.stock.results)}")
        print(f"instrumented: {' '.join(replay.instrumented.results)}")
    elif args.command == "time":
        output = args.output or args.capture_dir / "stock-timing.json"
        write_timing_report(output, report)
        print(report.summary())
        print(f"report: {output}")
    else:
        output = args.output or args.capture_dir / "z3-comparison.json"
        write_comparison_report(output, report)
        print(report.summary())
        print(f"report: {output}")
    return 0


def _builder_manifest(build_dir: Path | None) -> dict[str, Any]:
    if build_dir is not None:
        return load_builder_manifest(build_dir)
    if sys.stdin.isatty():
        raise ReplayError(
            "pipe z3-builder output into this command or pass --z3-build-dir"
        )
    value = json.load(sys.stdin)
    if not isinstance(value, dict):
        raise ReplayError("z3-builder input must be a JSON object")
    return value


if __name__ == "__main__":
    raise SystemExit(main())
