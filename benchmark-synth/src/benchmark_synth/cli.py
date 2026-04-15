"""CLI entry points for benchmark synthesis."""

from __future__ import annotations

import argparse
from pathlib import Path

from .export_dataset import export_placeholder
from .generate import GenerateConfig, generate_corpus
from .ir import FamilyName, PropertyFamily, SkeletonType
from .run_yardbird import run_corpus, write_runs


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="benchmark-synth")
    subparsers = parser.add_subparsers(dest="command", required=True)

    generate_parser = subparsers.add_parser("generate")
    generate_parser.add_argument("--output-dir", type=Path, required=True)
    generate_parser.add_argument("--seed", type=int, required=True)
    generate_parser.add_argument("--count", type=int, required=True)
    generate_parser.add_argument(
        "--family",
        type=FamilyName,
        choices=list(FamilyName),
        required=True,
    )
    generate_parser.add_argument(
        "--skeleton",
        type=SkeletonType,
        choices=list(SkeletonType),
        required=True,
    )
    generate_parser.add_argument(
        "--property-family",
        type=PropertyFamily,
        choices=list(PropertyFamily),
        required=True,
    )
    generate_parser.add_argument("--bug-ratio", type=float, default=0.0)

    validate_parser = subparsers.add_parser("validate")
    validate_parser.add_argument("--corpus-dir", type=Path, required=True)

    run_parser = subparsers.add_parser("run-yardbird")
    run_parser.add_argument("--corpus-dir", type=Path, required=True)
    run_parser.add_argument("--output-dir", type=Path, required=True)
    run_parser.add_argument("--yardbird-bin", type=Path, required=True)
    run_parser.add_argument("--strategy", required=True)
    run_parser.add_argument("--depth", type=int, required=True)
    run_parser.add_argument("--cost-function")

    export_parser = subparsers.add_parser("export-dataset")
    export_parser.add_argument("--output-file", type=Path, required=True)

    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()

    if args.command == "generate":
        generate_corpus(
            GenerateConfig(
                output_dir=args.output_dir,
                seed=args.seed,
                count=args.count,
                family=args.family,
                skeleton=args.skeleton,
                property_family=args.property_family,
                bug_ratio=args.bug_ratio,
            )
        )
        return 0

    if args.command == "validate":
        benchmark_count = len(list((args.corpus_dir / "benchmarks").glob("*.vmt")))
        print(f"found {benchmark_count} benchmarks")
        return 0

    if args.command == "run-yardbird":
        args.output_dir.mkdir(parents=True, exist_ok=True)
        entries = run_corpus(
            args.corpus_dir,
            yardbird_bin=args.yardbird_bin,
            strategy=args.strategy,
            depth=args.depth,
            cost_function=args.cost_function,
        )
        write_runs(args.output_dir / "run-manifest.json", entries)
        return 0

    if args.command == "export-dataset":
        export_placeholder(args.output_file)
        return 0

    parser.error(f"unsupported command: {args.command}")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
