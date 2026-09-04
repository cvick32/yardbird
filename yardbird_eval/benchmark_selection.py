from __future__ import annotations

from pathlib import Path
from typing import Any

from .common import BENCHMARK_ROOT, load_json


DEFAULT_DIFFICULT_THRESHOLD_SECONDS = 30.0
FORMULA_RESEARCH_COHORT = (
    Path(__file__).resolve().parent / "cohorts" / "formula-transformations.json"
)


def _strategy_identity(result: dict[str, Any]) -> str | None:
    strategy = str(result.get("strategy", "")).lower()
    cost_function = str(result.get("cost_function", "")).lower()
    if strategy == "concrete":
        return "concrete"
    egraph_builder = str(result.get("egraph_builder") or "full").lower()
    if (
        strategy == "abstract"
        and cost_function == "bmc-cost"
        and egraph_builder == "full"
    ):
        return "abstract-bmc-cost"
    return None


def _timed_out(result: dict[str, Any]) -> bool:
    outcome = result.get("result")
    return isinstance(outcome, dict) and "Timeout" in outcome


def _succeeded(result: dict[str, Any]) -> bool:
    outcome = result.get("result")
    return isinstance(outcome, dict) and "Success" in outcome


def _normalize_example_path(example: str) -> str:
    normalized = example.replace("\\", "/")
    marker = "examples/"
    marker_index = normalized.find(marker)
    if marker_index >= 0:
        return normalized[marker_index:]
    return normalized


def _suite_files_from_manifest(manifest_path: Path) -> list[Path]:
    manifest = load_json(manifest_path)
    files: list[Path] = []
    for subrun in manifest.get("subruns", []):
        raw_path = subrun.get("result_path")
        if not raw_path:
            continue
        candidate = Path(raw_path).expanduser()
        if not candidate.is_absolute():
            candidate = (manifest_path.parent / candidate).resolve()
        if candidate.exists():
            files.append(candidate)

    files.extend(manifest_path.parent.glob("raw/**/*.json"))
    return sorted(set(files))


def _source_suite_files(source: str) -> tuple[str, list[Path]]:
    source_path = Path(source).expanduser()
    if source_path.exists():
        source_path = source_path.resolve()
        if source_path.is_dir():
            manifest_path = source_path / "run.json"
            if not manifest_path.exists():
                raise FileNotFoundError(
                    f"Difficult benchmark source has no run.json: {source_path}"
                )
            return str(manifest_path), _suite_files_from_manifest(manifest_path)

        payload = load_json(source_path)
        if isinstance(payload, dict) and "subruns" in payload:
            return str(source_path), _suite_files_from_manifest(source_path)
        if isinstance(payload, dict) and "benchmarks" in payload:
            return str(source_path), [source_path]
        raise RuntimeError(
            f"Difficult benchmark source is not a run manifest or Garden result: {source_path}"
        )

    manifest_path = BENCHMARK_ROOT / source / "run.json"
    if manifest_path.exists():
        return source, _suite_files_from_manifest(manifest_path)
    raise FileNotFoundError(f"Unknown difficult benchmark source: {source}")


def _source_has_baselines(suite_files: list[Path]) -> bool:
    identities: set[str] = set()
    for suite_file in suite_files:
        suite = load_json(suite_file, default={})
        for benchmark in suite.get("benchmarks", []):
            for result in benchmark.get("result", []):
                identity = _strategy_identity(result)
                if identity:
                    identities.add(identity)
    return {"abstract-bmc-cost", "concrete"}.issubset(identities)


def _auto_source() -> tuple[str, list[Path]]:
    candidates: list[tuple[str, Path]] = []
    for manifest_path in BENCHMARK_ROOT.glob("*/run.json"):
        manifest = load_json(manifest_path, default={})
        benchmark_types = set(manifest.get("benchmark_types", []))
        if not {"deep-abstract", "deep-concrete"}.issubset(benchmark_types):
            continue
        if manifest.get("capture_solver_journals"):
            continue
        candidates.append((str(manifest.get("started_at", "")), manifest_path))

    for _, manifest_path in sorted(candidates, reverse=True):
        suite_files = _suite_files_from_manifest(manifest_path)
        if suite_files and _source_has_baselines(suite_files):
            return str(manifest_path.parent.name), suite_files

    raise RuntimeError(
        "Could not find a downloaded, capture-free main_eval run containing "
        "both deep-abstract and deep-concrete baseline results; pass a run id "
        "or Garden result JSON explicitly"
    )


def select_difficult_benchmarks(
    source: str,
    threshold_seconds: float = DEFAULT_DIFFICULT_THRESHOLD_SECONDS,
) -> dict[str, Any]:
    if threshold_seconds <= 0:
        raise ValueError("--difficult-threshold-seconds must be greater than zero")

    if source == "auto":
        resolved_source, suite_files = _auto_source()
    else:
        resolved_source, suite_files = _source_suite_files(source)

    if not suite_files:
        raise RuntimeError(f"No downloaded benchmark results found for {resolved_source}")

    threshold_ms = threshold_seconds * 1000.0
    selected: dict[str, set[str]] = {}
    baseline_identities: set[str] = set()
    for suite_file in suite_files:
        suite = load_json(suite_file, default={})
        for benchmark in suite.get("benchmarks", []):
            example = benchmark.get("example")
            if not isinstance(example, str):
                continue
            normalized_example = _normalize_example_path(example)
            for result in benchmark.get("result", []):
                identity = _strategy_identity(result)
                if identity is None:
                    continue
                baseline_identities.add(identity)
                run_time = result.get("run_time")
                over_threshold = isinstance(run_time, (int, float)) and (
                    run_time > threshold_ms
                )
                if _timed_out(result) or over_threshold:
                    selected.setdefault(normalized_example, set()).add(identity)

    if not selected:
        raise RuntimeError(
            f"No difficult benchmarks found in {resolved_source} above "
            f"{threshold_seconds:g} seconds"
        )

    return {
        "kind": "difficult-benchmarks",
        "source": resolved_source,
        "threshold_seconds": threshold_seconds,
        "baseline_strategies": sorted(baseline_identities),
        "benchmarks": sorted(selected),
        "reasons": {
            example: sorted(identities) for example, identities in sorted(selected.items())
        },
    }


def select_formula_research_cohort(source: str) -> dict[str, Any]:
    """Build the stable formula-transformation cohort plus live baseline failures."""
    if source == "auto":
        resolved_source, suite_files = _auto_source()
    else:
        resolved_source, suite_files = _source_suite_files(source)

    fixed = load_json(FORMULA_RESEARCH_COHORT)
    if not isinstance(fixed, dict):
        raise RuntimeError(f"Invalid formula cohort file: {FORMULA_RESEARCH_COHORT}")

    reasons: dict[str, set[str]] = {}
    for category, examples in fixed.items():
        if not isinstance(category, str) or not isinstance(examples, list):
            raise RuntimeError(f"Invalid formula cohort category: {category!r}")
        for example in examples:
            if not isinstance(example, str):
                raise RuntimeError(f"Invalid formula cohort benchmark: {example!r}")
            reasons.setdefault(_normalize_example_path(example), set()).add(category)

    baseline_outcomes: dict[str, dict[str, list[dict[str, Any]]]] = {}
    for suite_file in suite_files:
        suite = load_json(suite_file, default={})
        for benchmark in suite.get("benchmarks", []):
            example = benchmark.get("example")
            if not isinstance(example, str):
                continue
            normalized_example = _normalize_example_path(example)
            identities = baseline_outcomes.setdefault(normalized_example, {})
            for result in benchmark.get("result", []):
                identity = _strategy_identity(result)
                if identity:
                    identities.setdefault(identity, []).append(result)

    dynamic_category = "concrete-success-yardbird-timeout"
    for example, identities in baseline_outcomes.items():
        concrete_success = any(
            _succeeded(result) for result in identities.get("concrete", [])
        )
        abstract_timeout = any(
            _timed_out(result) for result in identities.get("abstract-bmc-cost", [])
        )
        if concrete_success and abstract_timeout:
            reasons.setdefault(example, set()).add(dynamic_category)

    return {
        "kind": "formula-research-cohort",
        "source": resolved_source,
        "benchmarks": sorted(reasons),
        "reasons": {
            example: sorted(categories)
            for example, categories in sorted(reasons.items())
        },
    }


def garden_filter_args(args: Any) -> list[str]:
    command_args: list[str] = []
    selection = getattr(args, "benchmark_selection", None)
    if selection:
        for benchmark in selection["benchmarks"]:
            command_args.extend(["--include", benchmark])
    if getattr(args, "limit", None) is not None:
        command_args.extend(["--limit", str(args.limit)])
    if getattr(args, "sample_seed", None) is not None:
        command_args.extend(["--sample-seed", str(args.sample_seed)])
    return command_args
