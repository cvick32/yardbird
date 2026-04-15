"""Corpus generation."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import random

from .families import build_single_loop_copy
from .ir import BenchmarkSpec, FamilyName, PropertyFamily, SkeletonType
from .lower_vmt import lower_benchmark
from .manifests import CorpusEntry, CorpusManifest, RejectionEntry
from .metadata import BenchmarkMetadata
from .mutators import apply_bug_mutation
from .naming import benchmark_filename, metadata_filename
from .validate import validate_structural


@dataclass(frozen=True)
class GenerateConfig:
    output_dir: Path
    seed: int
    count: int
    family: FamilyName
    skeleton: SkeletonType
    property_family: PropertyFamily
    bug_ratio: float


def generate_corpus(config: GenerateConfig) -> CorpusManifest:
    if config.family != FamilyName.COPY:
        raise NotImplementedError("only the copy family is implemented in the first slice")
    if config.skeleton != SkeletonType.SINGLE_LOOP:
        raise NotImplementedError("only single_loop is implemented in the first slice")
    if config.property_family != PropertyFamily.POINTWISE:
        raise NotImplementedError("only pointwise properties are implemented in the first slice")

    benchmark_dir = config.output_dir / "benchmarks"
    metadata_dir = config.output_dir / "metadata"
    benchmark_dir.mkdir(parents=True, exist_ok=True)
    metadata_dir.mkdir(parents=True, exist_ok=True)

    rng = random.Random(config.seed)
    entries: list[CorpusEntry] = []
    rejections: list[RejectionEntry] = []

    for ordinal in range(config.count):
        try:
            bug_flag = rng.random() < config.bug_ratio
            spec = _build_spec(config.seed, ordinal, bug_flag)
            validate_structural(spec)
            lowered = lower_benchmark(spec)
            metadata = spec.metadata()

            bench_path = benchmark_dir / benchmark_filename(spec.benchmark_name)
            meta_path = metadata_dir / metadata_filename(spec.benchmark_name)
            bench_path.write_text(lowered.vmt_text)
            metadata.write_json(meta_path)

            entries.append(
                CorpusEntry(
                    benchmark_name=spec.benchmark_name,
                    benchmark_path=str(bench_path),
                    metadata_path=str(meta_path),
                    bug_flag=spec.bug_flag,
                )
            )
        except Exception as exc:  # pragma: no cover - defensive bookkeeping
            rejections.append(
                RejectionEntry(
                    benchmark_name=f"rejected_seed{config.seed}_{ordinal:04d}",
                    reason=str(exc),
                )
            )

    manifest = CorpusManifest(
        corpus_name=config.output_dir.name,
        seed=config.seed,
        entries=entries,
        rejections=rejections,
    )
    manifest.write_json(config.output_dir / "manifest.json")
    return manifest


def _build_spec(seed: int, ordinal: int, bug_flag: bool) -> BenchmarkSpec:
    spec = build_single_loop_copy(seed=seed, ordinal=ordinal, bug_flag=False)
    if bug_flag:
        spec = apply_bug_mutation(spec, bug_kind=spec_bug_kind())
    return spec


def spec_bug_kind():
    from .ir import BugKind

    return BugKind.WRONG_WRITE_INDEX
