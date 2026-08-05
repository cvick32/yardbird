"""Compose the instrumentation-specific workbook section and its exports."""

from __future__ import annotations

import json
import statistics
from dataclasses import dataclass
from pathlib import Path

from .instrumentation_chart import write_instrumentation_chart
from .instrumentation_data import (
    aggregate_completed_by_strategy,
    aggregate_unavailable,
    write_instrumentation_csv,
)
from .typst import typst_table


@dataclass(frozen=True)
class InstrumentationReport:
    sections: list[str]
    assets: list[Path]
    exports: dict[str, object]


def build_instrumentation_report(
    manifest: dict, report_dir: Path
) -> InstrumentationReport:
    _clear_previous_assets(report_dir / "assets")
    instrumentation = manifest.get("instrumentation")
    if not isinstance(instrumentation, dict):
        return InstrumentationReport([], [], {})
    summary_value = instrumentation.get("comparison_summary_path")
    if not summary_value:
        return InstrumentationReport([], [], {})

    summary_path = Path(summary_value)
    summary = json.loads(summary_path.read_text())
    entries = summary.get("entries", [])
    completed = [
        entry for entry in entries if entry.get("comparison_status") == "completed"
    ]
    unavailable = [
        entry for entry in entries if entry.get("comparison_status") != "completed"
    ]
    csv_path = write_instrumentation_csv(
        report_dir / "data" / "instrumentation_comparisons.csv", entries
    )
    exports = {
        "instrumentation_summary": str(summary_path),
        "instrumentation_csv": str(csv_path),
    }

    if not completed:
        exports["instrumentation_figure_assets"] = []
        return InstrumentationReport(
            _unavailable_only_sections(unavailable), [], exports
        )

    strategies = aggregate_completed_by_strategy(completed)
    assets = [
        write_instrumentation_chart(
            report_dir / "assets" / "instrumentation_external.svg",
            strategies,
            kind="external",
        ),
        write_instrumentation_chart(
            report_dir / "assets" / "instrumentation_breakdown.svg",
            strategies,
            kind="breakdown",
        ),
    ]
    exports["instrumentation_figure_assets"] = [str(path) for path in assets]
    return InstrumentationReport(
        _completed_sections(summary, completed, unavailable, strategies),
        assets,
        exports,
    )


def _completed_sections(
    summary: dict,
    completed: list[dict],
    unavailable: list[dict],
    strategies: list[dict],
) -> list[str]:
    overheads = [entry["metrics"]["external_overhead_pct"] for entry in completed]
    fractions = [entry["metrics"]["array_fraction_pct"] for entry in completed]
    rows = [_strategy_row(strategy) for strategy in strategies]
    lines = [
        "#pagebreak()",
        "",
        "= Instrumented Z3 Replay Comparison",
        "",
        f"This section compares *{len(completed)} captured Yardbird solver sessions* "
        f"across *{len(strategies)} strategy groups* against matched stock and "
        "instrumented Z3 binaries. Each session reports the "
        f"median of {summary['repetitions']} paired repetitions after "
        f"{summary['warmups']} warmups; strategy rows are medians over every "
        "completed session in that group.",
        "",
        "External time is the solver pipe round trip. Internal time is measured inside "
        "instrumented Z3; the array envelope is a subset of that internal check time, "
        "and the residual contains SAT, EUF, arithmetic, other theories, and unclassified "
        "solver work.",
        "",
        typst_table(
            [
                "Sessions",
                "Strategies",
                "Unavailable",
                "Median overhead",
                "Median array share",
            ],
            [
                [
                    len(completed),
                    len(strategies),
                    len(unavailable),
                    f"{statistics.median(overheads):+.1f}%",
                    f"{statistics.median(fractions):.1f}%",
                ]
            ],
            columns="(.7fr, .7fr, .8fr, 1.1fr, 1.1fr)",
        ),
        "",
        '#image("assets/instrumentation_external.svg", width: 100%)',
        "",
        '#image("assets/instrumentation_breakdown.svg", width: 100%)',
        "",
        "== Strategy Summary",
        "",
        typst_table(
            [
                "Strategy",
                "Sessions",
                "Stock",
                "Instr. ext.",
                "Overhead",
                "Instr. int.",
                "Array",
                "Array share",
            ],
            rows,
            columns="(1.5fr, .55fr, .7fr, .7fr, .65fr, .7fr, .7fr, .65fr)",
            size="6.5pt",
        ),
        "",
        "The session-level CSV retains every benchmark comparison used in these aggregates.",
        "",
    ]
    if unavailable:
        lines.extend(_unavailable_sections(unavailable))
    return lines


def _strategy_row(strategy: dict) -> list[object]:
    metrics = strategy["metrics"]
    return [
        strategy["strategy_label"],
        strategy["session_count"],
        _milliseconds(metrics["stock_external_median_ns"]),
        _milliseconds(metrics["instrumented_external_median_ns"]),
        f"{metrics['external_overhead_pct']:+.1f}%",
        _milliseconds(metrics["instrumented_internal_median_ns"]),
        _milliseconds(metrics["array_envelope_median_ns"]),
        f"{metrics['array_fraction_pct']:.1f}%",
    ]


def _unavailable_only_sections(unavailable: list[dict]) -> list[str]:
    return [
        "#pagebreak()",
        "",
        "= Instrumented Z3 Replay Comparison",
        "",
        "No Yardbird run in this evaluation produced a completed solver capture, "
        "so no paired replay timing is available.",
        "",
        *_unavailable_sections(unavailable, include_heading=False),
    ]


def _unavailable_sections(
    unavailable: list[dict], *, include_heading: bool = True
) -> list[str]:
    lines = []
    if include_heading:
        lines.extend(["== Unavailable Comparisons", ""])
    lines.extend(
        [
            typst_table(
                ["Strategy", "Sessions", "Yardbird result", "Reason"],
                aggregate_unavailable(unavailable),
                columns="(1.2fr, .6fr, .8fr, 1.8fr)",
                size="7pt",
            ),
            "",
        ]
    )
    return lines


def _milliseconds(runtime_ns: int | float | None) -> str:
    if runtime_ns is None:
        return "-"
    return f"{runtime_ns / 1_000_000.0:.3f}ms"


def _clear_previous_assets(assets_dir: Path) -> None:
    for path in assets_dir.glob("instrumentation_*.svg"):
        if path.is_file():
            path.unlink()
