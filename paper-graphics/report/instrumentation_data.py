"""Session-level exports and strategy aggregation for instrumentation runs."""

from __future__ import annotations

import csv
import statistics
from pathlib import Path


METRIC_FIELDS = (
    "stock_external_median_ns",
    "instrumented_external_median_ns",
    "external_overhead_median_ns",
    "external_overhead_pct",
    "instrumented_internal_median_ns",
    "array_envelope_median_ns",
    "non_array_residual_median_ns",
    "array_fraction_pct",
)


def strategy_label(entry: dict) -> str:
    strategy = str(entry.get("strategy", "unknown"))
    cost = entry.get("cost_function")
    if strategy == "abstract" and cost:
        return f"{strategy}/{cost}"
    return strategy


def aggregate_completed_by_strategy(entries: list[dict]) -> list[dict]:
    grouped: dict[str, list[dict]] = {}
    for entry in entries:
        grouped.setdefault(strategy_label(entry), []).append(entry)

    summaries = []
    for label, sessions in sorted(grouped.items()):
        metrics = {
            field: statistics.median(session["metrics"][field] for session in sessions)
            for field in METRIC_FIELDS
        }
        summaries.append(
            {
                "strategy_label": label,
                "session_count": len(sessions),
                "metrics": metrics,
            }
        )
    return summaries


def aggregate_unavailable(entries: list[dict]) -> list[list[object]]:
    grouped: dict[tuple[str, str, str], int] = {}
    for entry in entries:
        key = (
            strategy_label(entry),
            str(entry.get("yardbird_result_type", "unknown")),
            str(entry.get("comparison_error", "unknown")),
        )
        grouped[key] = grouped.get(key, 0) + 1
    return [
        [strategy, count, result, reason]
        for (strategy, result, reason), count in sorted(grouped.items())
    ]


def write_instrumentation_csv(path: Path, entries: list[dict]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    fields = [
        "run_type",
        "example",
        "solver",
        "strategy",
        "cost_function",
        "depth",
        "yardbird_result_type",
        "yardbird_run_time_ms",
        "comparison_status",
        "comparison_error",
        "capture_dir",
        "comparison_path",
        "check_count",
        "depth_count",
        *METRIC_FIELDS,
    ]
    with path.open("w", newline="", encoding="utf-8") as output:
        writer = csv.DictWriter(output, fieldnames=fields)
        writer.writeheader()
        for entry in entries:
            metrics = entry.get("metrics") or {}
            writer.writerow(
                {field: metrics.get(field, entry.get(field, "")) for field in fields}
            )
    return path
