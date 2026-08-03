#!/usr/bin/env python3
"""Replay a Yardbird solver capture through a matched Z3 build pair."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from z3_profile import ReplayError, load_builder_manifest, replay_build_pair


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
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command != "replay":
        raise AssertionError(f"unhandled command {args.command}")

    try:
        builder_manifest = _builder_manifest(args.z3_build_dir)
        replay = replay_build_pair(
            args.capture_dir,
            builder_manifest,
            timeout_seconds=args.timeout,
        )
    except (ReplayError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1

    print(f"expected:     {' '.join(replay.expected)}")
    print(f"stock:        {' '.join(replay.stock.results)}")
    print(f"instrumented: {' '.join(replay.instrumented.results)}")
    return 0


def _builder_manifest(build_dir: Path | None) -> dict[str, Any]:
    if build_dir is not None:
        return load_builder_manifest(build_dir)
    if sys.stdin.isatty():
        raise ReplayError(
            "pipe z3-builder output into replay or pass --z3-build-dir"
        )
    value = json.load(sys.stdin)
    if not isinstance(value, dict):
        raise ReplayError("z3-builder input must be a JSON object")
    return value


if __name__ == "__main__":
    raise SystemExit(main())
