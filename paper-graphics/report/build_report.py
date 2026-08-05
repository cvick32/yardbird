#!/usr/bin/env python3

from __future__ import annotations

import argparse
import csv
import html
import json
import statistics
import subprocess
import sys
import tempfile
from datetime import datetime
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]
PAPER_GRAPHICS_ROOT = PROJECT_ROOT / "paper-graphics"
TEMPLATE_PATH = PAPER_GRAPHICS_ROOT / "report" / "template.typ"
sys.path.insert(0, str(PAPER_GRAPHICS_ROOT))

from main import choose_baseline_strategy, generate_figures  # noqa: E402
from src.analysis import build_analysis, write_analysis_exports  # noqa: E402
from src.benchmark_parsing import BenchmarkParser  # noqa: E402


FIGURE_PREFIXES = (
    "runtime_scatter_",
    "instantiation_scatter_",
    "runtime_cactus_plot",
    "instantiation_cactus_plot",
)
GENERATED_TEX_PATTERNS = (
    "all_benchmarks_table.tex",
    "summary_statistics.tex",
    "shared_benchmark_analysis.tex",
    "runtime_*.tex",
    "instantiation_*.tex",
    "unique_solves_*.tex",
)
GENERATED_ASSET_PATTERNS = ("runtime_*.pdf", "instantiation_*.pdf")
INSTRUMENTATION_ASSET_PATTERNS = ("instrumentation_*.svg",)


def load_json(path: Path) -> dict:
    return json.loads(path.read_text())


def write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


def run_command(
    args: list[str], cwd: Path | None = None
) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        args,
        cwd=str(cwd) if cwd else None,
        text=True,
        capture_output=True,
    )
    if result.returncode != 0:
        message = result.stderr.strip() or result.stdout.strip()
        raise RuntimeError(f"{' '.join(args)}\n{message}")
    return result


def benchmark_groupings(json_files: list[Path]) -> tuple[dict, set[str], list]:
    parser = BenchmarkParser(json_files)
    grouped: dict[str, dict[str, object]] = {}
    strategy_keys: set[str] = set()
    for result in parser.all_results:
        grouped.setdefault(result.example_name, {})
        strategy_key = result.get_strategy_id()
        strategy_keys.add(strategy_key)
        grouped[result.example_name][strategy_key] = result
    return grouped, strategy_keys, parser.all_results


def figure_tex_paths(tex_dir: Path) -> list[Path]:
    paths = []
    for path in sorted(tex_dir.glob("*.tex")):
        if any(path.stem.startswith(prefix) for prefix in FIGURE_PREFIXES):
            paths.append(path)
    return paths


def table_tex_paths(tex_dir: Path) -> list[Path]:
    figure_paths = set(figure_tex_paths(tex_dir))
    return [path for path in sorted(tex_dir.glob("*.tex")) if path not in figure_paths]


def clear_generated_files(directory: Path, patterns: tuple[str, ...]) -> None:
    for pattern in patterns:
        for path in directory.glob(pattern):
            if path.is_file():
                path.unlink()


def latex_wrapper_for(fragment_path: Path) -> str:
    fragment = fragment_path.resolve().as_posix()
    return rf"""\documentclass[11pt]{{article}}
\usepackage[margin=0.5in]{{geometry}}
\usepackage{{pgfplots}}
\pgfplotsset{{compat=1.18}}
\usepackage{{xcolor}}
\definecolor{{softBlue}}{{RGB}}{{80, 132, 196}}
\definecolor{{softBrown}}{{RGB}}{{156, 117, 95}}
\definecolor{{softRed}}{{RGB}}{{196, 78, 82}}
\definecolor{{softGreen}}{{RGB}}{{107, 168, 79}}
\definecolor{{softPurple}}{{RGB}}{{129, 114, 179}}
\definecolor{{softOrange}}{{RGB}}{{221, 132, 82}}
\definecolor{{softYellow}}{{RGB}}{{204, 185, 116}}
\definecolor{{softTeal}}{{RGB}}{{78, 163, 151}}
\pagestyle{{empty}}
\begin{{document}}
\input{{{fragment}}}
\end{{document}}
"""


def compile_figure_fragment(fragment_path: Path, assets_dir: Path) -> Path:
    assets_dir.mkdir(parents=True, exist_ok=True)
    assets_dir = assets_dir.resolve()
    output_pdf = assets_dir / f"{fragment_path.stem}.pdf"
    with tempfile.TemporaryDirectory(prefix=f"{fragment_path.stem}_") as temp_dir:
        temp_root = Path(temp_dir)
        wrapper_path = temp_root / "wrapper.tex"
        wrapper_path.write_text(latex_wrapper_for(fragment_path))
        run_command(
            [
                "pdflatex",
                "-interaction=nonstopmode",
                "-halt-on-error",
                f"-output-directory={assets_dir}",
                str(wrapper_path),
            ],
            cwd=temp_root,
        )
        generated = assets_dir / "wrapper.pdf"
        if generated.exists():
            generated.rename(output_pdf)
        cropped_pdf = assets_dir / f"{fragment_path.stem}.cropped.pdf"
        run_command(
            ["pdfcrop", "--margins", "4", str(output_pdf), str(cropped_pdf)],
            cwd=assets_dir,
        )
        cropped_pdf.replace(output_pdf)
        for suffix in (".aux", ".log", ".out"):
            temp_artifact = assets_dir / f"wrapper{suffix}"
            if temp_artifact.exists():
                temp_artifact.unlink()
    return output_pdf


def figure_title(fragment: Path) -> str:
    title = fragment.stem.replace("_", " ").strip()
    return " ".join(word.capitalize() for word in title.split())


def typst_cell(value: object, *, bold: bool = False) -> str:
    weight = 'weight: "bold", ' if bold else ""
    encoded = json.dumps(str(value), ensure_ascii=False)
    return f"[#text({weight}{encoded})]"


def typst_table(
    headers: list[str],
    rows: list[list[object]],
    *,
    columns: str,
    size: str = "8pt",
) -> str:
    lines = [
        f"#text(size: {size})[",
        "  #table(",
        f"    columns: {columns},",
        "    inset: (x: 4pt, y: 3pt),",
        "    stroke: 0.3pt + luma(205),",
        "    table.header(",
    ]
    lines.extend(f"      {typst_cell(header, bold=True)}," for header in headers)
    lines.extend(["    ),"])
    for row in rows:
        lines.extend(f"    {typst_cell(value)}," for value in row)
    lines.extend(["  )", "]"])
    return "\n".join(lines)


def short_benchmark_name(name: str) -> str:
    return name.removeprefix("examples/array/").removesuffix(".vmt")


def seconds(runtime_ms: int | float | None) -> str:
    if runtime_ms is None:
        return "-"
    return f"{runtime_ms / 1000.0:.3f}s"


def milliseconds(runtime_ns: int | float | None) -> str:
    if runtime_ns is None:
        return "-"
    return f"{runtime_ns / 1_000_000.0:.3f}ms"


def instrumentation_label(entry: dict) -> str:
    benchmark = short_benchmark_name(str(entry.get("example", "unknown")))
    strategy = str(entry.get("strategy", "unknown"))
    cost = entry.get("cost_function")
    if strategy == "abstract" and cost:
        strategy = f"{strategy}/{cost}"
    return f"{benchmark} - {strategy} - d{entry.get('depth', '?')}"


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
        "stock_external_median_ns",
        "instrumented_external_median_ns",
        "external_overhead_median_ns",
        "external_overhead_pct",
        "instrumented_internal_median_ns",
        "array_envelope_median_ns",
        "non_array_residual_median_ns",
        "array_fraction_pct",
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


def _svg_text(x: float, y: float, value: str, **attributes: object) -> str:
    attrs = " ".join(
        f'{name.replace("_", "-")}="{item}"' for name, item in attributes.items()
    )
    return f'<text x="{x}" y="{y}" {attrs}>{html.escape(value)}</text>'


def write_instrumentation_chart(
    path: Path,
    entries: list[dict],
    *,
    kind: str,
) -> Path:
    shown = entries[:20]
    width = 1200
    label_width = 390
    chart_width = 730
    top = 100
    row_height = 45
    height = top + max(1, len(shown)) * row_height + 45

    if kind == "external":
        title = "Captured-session replay time: stock vs instrumented Z3"
        first_label, second_label = "Stock external", "Instrumented external"
        first_color, second_color = "#5084c4", "#c44e52"
        values = [
            (
                entry["metrics"]["stock_external_median_ns"],
                entry["metrics"]["instrumented_external_median_ns"],
            )
            for entry in shown
        ]
    elif kind == "breakdown":
        title = "Instrumented Z3 internal time: array envelope vs residual"
        first_label, second_label = "Array envelope", "Non-array residual"
        first_color, second_color = "#4ea397", "#dd8452"
        values = [
            (
                entry["metrics"]["array_envelope_median_ns"],
                entry["metrics"]["non_array_residual_median_ns"],
            )
            for entry in shown
        ]
    else:
        raise ValueError(f"Unknown instrumentation chart kind: {kind}")

    maximum = max((first + second for first, second in values), default=1)
    if kind == "external":
        maximum = max((max(first, second) for first, second in values), default=1)
    maximum = max(maximum, 1)
    scale = chart_width / maximum

    lines = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="white"/>',
        _svg_text(
            12, 32, title, font_family="sans-serif", font_size="30", font_weight="bold"
        ),
        f'<rect x="{label_width}" y="39" width="12" height="12" fill="{first_color}"/>',
        _svg_text(
            label_width + 18, 64, first_label, font_family="sans-serif", font_size="20"
        ),
        f'<rect x="{label_width + 165}" y="39" width="12" height="12" fill="{second_color}"/>',
        _svg_text(
            label_width + 183,
            64,
            second_label,
            font_family="sans-serif",
            font_size="20",
        ),
    ]
    for fraction in (0.0, 0.5, 1.0):
        x = label_width + chart_width * fraction
        lines.append(
            f'<line x1="{x:.1f}" y1="{top - 8}" x2="{x:.1f}" y2="{height - 30}" stroke="#dddddd" stroke-width="1"/>'
        )
        lines.append(
            _svg_text(
                x,
                height - 10,
                f"{maximum * fraction / 1_000_000:.2f}ms",
                font_family="sans-serif",
                font_size="16",
                text_anchor="middle",
                fill="#555555",
            )
        )

    for row, (entry, (first, second)) in enumerate(zip(shown, values)):
        y = top + row * row_height
        label = instrumentation_label(entry)
        if len(label) > 54:
            label = label[:51] + "..."
        lines.append(
            _svg_text(
                label_width - 8,
                y + 17,
                label,
                font_family="sans-serif",
                font_size="18",
                text_anchor="end",
            )
        )
        if kind == "external":
            lines.extend(
                [
                    f'<rect x="{label_width}" y="{y + 5}" width="{first * scale:.2f}" height="9" fill="{first_color}"/>',
                    f'<rect x="{label_width}" y="{y + 17}" width="{second * scale:.2f}" height="9" fill="{second_color}"/>',
                ]
            )
        else:
            first_width = first * scale
            lines.extend(
                [
                    f'<rect x="{label_width}" y="{y + 8}" width="{first_width:.2f}" height="16" fill="{first_color}"/>',
                    f'<rect x="{label_width + first_width:.2f}" y="{y + 8}" width="{second * scale:.2f}" height="16" fill="{second_color}"/>',
                ]
            )
    lines.append("</svg>")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path


def instrumentation_workbook_sections(
    manifest: dict, report_dir: Path
) -> tuple[list[str], dict[str, object]]:
    instrumentation = manifest.get("instrumentation")
    if not isinstance(instrumentation, dict):
        return [], {}
    summary_value = instrumentation.get("comparison_summary_path")
    if not summary_value:
        return [], {}
    summary_path = Path(summary_value)
    summary = load_json(summary_path)
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
    if not completed:
        rows = [
            [
                instrumentation_label(entry),
                entry.get("yardbird_result_type", "unknown"),
                entry.get("comparison_error", "unknown"),
            ]
            for entry in unavailable[:20]
        ]
        return [
            "#pagebreak()",
            "",
            "= Instrumented Z3 Replay Comparison",
            "",
            "No Yardbird run in this evaluation produced a completed solver capture, "
            "so no paired replay timing is available.",
            "",
            typst_table(
                ["Session", "Yardbird result", "Reason"],
                rows,
                columns="(1.4fr, .8fr, 1.8fr)",
                size="7pt",
            ),
            "",
        ], {
            "instrumentation_summary": str(summary_path),
            "instrumentation_csv": str(csv_path),
            "instrumentation_figure_assets": [],
        }

    external_chart = write_instrumentation_chart(
        report_dir / "assets" / "instrumentation_external.svg",
        completed,
        kind="external",
    )
    breakdown_chart = write_instrumentation_chart(
        report_dir / "assets" / "instrumentation_breakdown.svg",
        completed,
        kind="breakdown",
    )
    overheads = [entry["metrics"]["external_overhead_pct"] for entry in completed]
    fractions = [entry["metrics"]["array_fraction_pct"] for entry in completed]
    rows = []
    for entry in completed[:40]:
        metrics = entry["metrics"]
        rows.append(
            [
                instrumentation_label(entry),
                milliseconds(metrics["stock_external_median_ns"]),
                milliseconds(metrics["instrumented_external_median_ns"]),
                f"{metrics['external_overhead_pct']:+.1f}%",
                milliseconds(metrics["instrumented_internal_median_ns"]),
                milliseconds(metrics["array_envelope_median_ns"]),
                f"{metrics['array_fraction_pct']:.1f}%",
            ]
        )

    lines = [
        "#pagebreak()",
        "",
        "= Instrumented Z3 Replay Comparison",
        "",
        f"This section compares *{len(completed)} captured Yardbird solver sessions* "
        "against matched stock and instrumented Z3 binaries. Each entry reports the "
        f"median of {summary['repetitions']} paired repetitions after "
        f"{summary['warmups']} warmups.",
        "",
        "External time is the solver pipe round trip. Internal time is measured inside "
        "instrumented Z3; the array envelope is a subset of that internal check time, "
        "and the residual contains SAT, EUF, arithmetic, other theories, and unclassified "
        "solver work.",
        "",
        typst_table(
            ["Sessions", "Unavailable", "Median overhead", "Median array share"],
            [
                [
                    len(completed),
                    len(unavailable),
                    f"{statistics.median(overheads):+.1f}%",
                    f"{statistics.median(fractions):.1f}%",
                ]
            ],
            columns="(.8fr, .8fr, 1.1fr, 1.1fr)",
        ),
        "",
        '#image("assets/instrumentation_external.svg", width: 100%)',
        "",
        '#image("assets/instrumentation_breakdown.svg", width: 100%)',
        "",
        f"Charts show {min(len(completed), 20)} of {len(completed)} completed sessions; "
        "the detail table and CSV retain the complete comparison set.",
        "",
        "== Session Details",
        "",
        typst_table(
            [
                "Session",
                "Stock",
                "Instr. ext.",
                "Overhead",
                "Instr. int.",
                "Array",
                "Array share",
            ],
            rows,
            columns="(2fr, .75fr, .75fr, .7fr, .75fr, .75fr, .7fr)",
            size="6.5pt",
        ),
        "",
    ]
    if len(completed) > len(rows):
        lines.extend(
            [
                f"Showing {len(rows)} of {len(completed)} completed sessions; see "
                "`data/instrumentation_comparisons.csv` for all rows.",
                "",
            ]
        )
    if unavailable:
        unavailable_rows = [
            [
                instrumentation_label(entry),
                entry.get("yardbird_result_type", "unknown"),
                entry.get("comparison_error", "unknown"),
            ]
            for entry in unavailable[:20]
        ]
        lines.extend(
            [
                "== Unavailable Comparisons",
                "",
                typst_table(
                    ["Session", "Yardbird result", "Reason"],
                    unavailable_rows,
                    columns="(1.4fr, .8fr, 1.8fr)",
                    size="7pt",
                ),
                "",
            ]
        )

    return lines, {
        "instrumentation_summary": str(summary_path),
        "instrumentation_csv": str(csv_path),
        "instrumentation_figure_assets": [
            str(external_chart),
            str(breakdown_chart),
        ],
    }


def analysis_workbook_sections(analysis: dict) -> list[str]:
    overview = analysis["overview"]
    baseline_name = analysis["baseline_display_name"]
    lines = [
        "= Executive Summary",
        "",
        f"This run contains *{overview['benchmark_count']} benchmarks* and "
        f"*{overview['strategy_count']} strategies*. The combined portfolio solved "
        f"*{overview['portfolio_solved_count']} / {overview['benchmark_count']}* benchmarks.",
        "",
        f"All comparisons use *{baseline_name}* as the baseline. Runtime speedup is "
        "baseline runtime divided by candidate runtime; values above 1x favor the candidate.",
        "",
    ]
    if overview["result_count"] != overview["expected_result_count"]:
        lines.extend(
            [
                '#block(fill: rgb("fff4d6"), inset: 8pt, radius: 3pt)['
                f"*Coverage note:* Only {overview['result_count']} of "
                f"{overview['expected_result_count']} expected result rows were present. "
                "Missing rows are reported separately and are not counted as failures.]",
                "",
            ]
        )

    strategy_rows = []
    for summary in analysis["strategy_summaries"]:
        median = summary["median_solved_runtime_s"]
        median_text = f"{median:.3f}s" if median is not None else "-"
        solve_rate = summary["solve_rate_pct"]
        solve_rate_text = f"{solve_rate:.1f}%" if solve_rate is not None else "-"
        strategy_rows.append(
            [
                summary["display_name"],
                summary["solved"],
                summary["unsolved"],
                summary["missing_results"],
                solve_rate_text,
                median_text,
                summary["fastest_solve_count"],
                summary["exclusive_solve_count"],
            ]
        )
    lines.extend(
        [
            "== Strategy Coverage",
            "",
            typst_table(
                [
                    "Strategy",
                    "Solved",
                    "Unsolved",
                    "Missing",
                    "Rate",
                    "Median",
                    "Fastest",
                    "Exclusive",
                ],
                strategy_rows,
                columns="(1.6fr, .6fr, .7fr, .65fr, .65fr, .8fr, .65fr, .7fr)",
            ),
            "",
            "_Fastest_ counts the lowest observed runtime among successful strategies for each "
            "benchmark. _Exclusive_ means no other strategy in this run solved that benchmark.",
            "",
        ]
    )

    comparison_rows = []
    for comparison in analysis["baseline_comparisons"]:
        speedup = comparison["geomean_runtime_speedup"]
        speedup_text = f"{speedup:.3f}x" if speedup is not None else "-"
        comparison_rows.append(
            [
                comparison["candidate_display_name"],
                comparison["candidate_solved"],
                f"{comparison['solve_coverage_delta']:+d}",
                f"{comparison['candidate_only_solved_count']} / "
                f"{comparison['baseline_only_solved_count']}",
                comparison["both_solved_count"],
                f"{comparison['runtime_win_count']} / "
                f"{comparison['runtime_tie_count']} / "
                f"{comparison['runtime_loss_count']}",
                speedup_text,
            ]
        )
    if comparison_rows:
        lines.extend(
            [
                "== Baseline Comparisons",
                "",
                typst_table(
                    [
                        "Candidate",
                        "Solved",
                        "Delta",
                        "Exclusive C/B",
                        "Shared",
                        "Win/Tie/Loss",
                        "Geo speedup",
                    ],
                    comparison_rows,
                    columns="(1.6fr, .55fr, .55fr, .9fr, .6fr, 1fr, .85fr)",
                ),
                "",
                f"Runtime wins and losses use a "
                f"{analysis['runtime_tie_tolerance_pct']:.1f}% tie band.",
                "",
            ]
        )

    for comparison in analysis["baseline_comparisons"]:
        candidate_name = comparison["candidate_display_name"]
        speedup = comparison["geomean_runtime_speedup"]
        speedup_text = f"{speedup:.3f}x" if speedup is not None else "n/a"
        lines.extend(
            [
                "#pagebreak()",
                "",
                f"= {candidate_name} vs {baseline_name}",
                "",
                f"*Solve coverage:* {comparison['candidate_solved']} vs "
                f"{comparison['baseline_solved']} "
                f"({comparison['solve_coverage_delta']:+d}). "
                f"The candidate uniquely solved {comparison['candidate_only_solved_count']} "
                f"and the baseline uniquely solved {comparison['baseline_only_solved_count']}.",
                "",
                f"*Shared solved performance:* {comparison['runtime_win_count']} runtime wins, "
                f"{comparison['runtime_tie_count']} ties, and "
                f"{comparison['runtime_loss_count']} losses across "
                f"{comparison['both_solved_count']} shared solves. Geometric-mean speedup: "
                f"*{speedup_text}*.",
                "",
            ]
        )

        for title, key, runtime_key, result_key in (
            (
                "Candidate-only Solves",
                "candidate_only_solves",
                "candidate_runtime_ms",
                "baseline_result_type",
            ),
            (
                "Baseline-only Solves",
                "baseline_only_solves",
                "baseline_runtime_ms",
                "candidate_result_type",
            ),
        ):
            rows = comparison[key]
            if not rows:
                continue
            table_rows = [
                [
                    short_benchmark_name(row["benchmark"]),
                    seconds(row[runtime_key]),
                    row[result_key] or "missing",
                ]
                for row in rows[:10]
            ]
            lines.extend(
                [
                    f"== {title}",
                    "",
                    typst_table(
                        ["Benchmark", "Solved runtime", "Other result"],
                        table_rows,
                        columns="(1fr, 1.1in, 1.1in)",
                    ),
                    "",
                ]
            )
            if len(rows) > len(table_rows):
                lines.extend(
                    [
                        f"Showing {len(table_rows)} of {len(rows)}; see "
                        "`data/benchmark_comparisons.csv` for the full list.",
                        "",
                    ]
                )

        for title, key in (
            ("Largest Runtime Improvements", "top_runtime_wins"),
            ("Largest Runtime Regressions", "top_runtime_losses"),
        ):
            rows = comparison[key][:8]
            if not rows:
                continue
            table_rows = [
                [
                    short_benchmark_name(row["benchmark"]),
                    seconds(row["candidate_runtime_ms"]),
                    seconds(row["baseline_runtime_ms"]),
                    f"{row['runtime_speedup']:.3f}x",
                ]
                for row in rows
            ]
            lines.extend(
                [
                    f"== {title}",
                    "",
                    typst_table(
                        ["Benchmark", "Candidate", "Baseline", "Speedup"],
                        table_rows,
                        columns="(1fr, .85in, .85in, .75in)",
                    ),
                    "",
                ]
            )

    return lines


def workbook_body(
    manifest: dict,
    analysis: dict,
    figure_assets: list[Path],
    table_sources: list[Path],
    instrumentation_sections: list[str],
) -> str:
    benchmark_types = ", ".join(manifest.get("benchmark_types", []))
    lines = [
        TEMPLATE_PATH.read_text().rstrip(),
        "",
        "= Yardbird Evaluation Workbook",
        "",
        f"*Run ID:* `{manifest['run_id']}`",
        "",
        f"*Name:* `{manifest.get('name', manifest['run_id'])}`",
        "",
        f"*Environment:* `{manifest['env']}`",
        "",
        f"*Status:* `{manifest['status']}`",
        "",
        f"*Benchmark Types:* `{benchmark_types}`",
        "",
        f"*Started:* `{manifest['started_at']}`",
        "",
    ]

    if manifest.get("completed_at"):
        lines.extend([f"*Completed:* `{manifest['completed_at']}`", ""])

    lines.extend(
        [
            "*Subruns:*",
            "",
        ]
    )
    for subrun in manifest["subruns"]:
        detail = f"- `{subrun['benchmark_type']}`: `{subrun['status']}`"
        if subrun.get("mode") == "aws":
            detail += f" via `{subrun.get('instance_id', 'unknown-instance')}`"
        lines.append(detail)
    lines.append("")

    lines.extend(analysis_workbook_sections(analysis))
    lines.extend(instrumentation_sections)

    for asset in figure_assets:
        rel_asset = asset.relative_to(asset.parent.parent).as_posix()
        lines.extend(
            [
                "#pagebreak()",
                "",
                f"= {figure_title(asset)}",
                "",
                f'#image("{rel_asset}", width: 100%)',
                "",
            ]
        )

    lines.extend(["#pagebreak()", "", "= Analysis Artifacts", ""])
    lines.extend(
        [
            "Reusable data generated with this workbook:",
            "",
            "- `analysis.json`: complete structured analysis, including notable benchmark lists",
            "- `analysis.md`: human-readable analysis summary",
            "- `data/strategy_summary.csv`: one row per strategy",
            "- `data/baseline_comparisons.csv`: one row per candidate/baseline comparison",
            "- `data/benchmark_results.csv`: normalized benchmark/strategy results",
            "- `data/benchmark_comparisons.csv`: benchmark-level win/loss classification",
            "",
            "== Supplemental LaTeX/TikZ",
            "",
        ]
    )
    if table_sources:
        lines.append(
            "The following paper-oriented LaTeX/TikZ tables are also available:"
        )
        lines.append("")
        for table in table_sources:
            rel_table = table.relative_to(table.parent.parent).as_posix()
            lines.append(f"- `{rel_table}`")
    else:
        lines.append("No tables were generated for this run.")
    lines.append("")

    return "\n".join(lines)


def build_report(manifest_path: Path, run_dir: Path) -> dict:
    manifest = load_json(manifest_path)
    report_dir = run_dir / "report"
    tex_dir = report_dir / "tex"
    assets_dir = report_dir / "assets"
    report_dir.mkdir(parents=True, exist_ok=True)
    tex_dir.mkdir(parents=True, exist_ok=True)
    assets_dir.mkdir(parents=True, exist_ok=True)
    clear_generated_files(tex_dir, GENERATED_TEX_PATTERNS)
    clear_generated_files(assets_dir, GENERATED_ASSET_PATTERNS)
    clear_generated_files(assets_dir, INSTRUMENTATION_ASSET_PATTERNS)
    (report_dir / "template.typ").write_text(TEMPLATE_PATH.read_text())

    json_files = [Path(subrun["result_path"]) for subrun in manifest["subruns"]]
    grouped, strategy_keys, all_results = benchmark_groupings(json_files)
    baseline_strategy = choose_baseline_strategy(strategy_keys)
    if baseline_strategy is None:
        raise RuntimeError("No benchmark strategies were found in the run artifacts")
    analysis = build_analysis(grouped, strategy_keys, baseline_strategy)
    data_exports = write_analysis_exports(report_dir, analysis)
    instrumentation_sections, instrumentation_exports = (
        instrumentation_workbook_sections(manifest, report_dir)
    )
    generate_figures(grouped, strategy_keys, all_results, tex_dir)

    figure_sources = figure_tex_paths(tex_dir)
    table_sources = table_tex_paths(tex_dir)
    compiled_assets = [
        compile_figure_fragment(path, assets_dir) for path in figure_sources
    ]

    workbook_typ = report_dir / "workbook.typ"
    workbook_pdf = report_dir / "workbook.pdf"
    workbook_typ.write_text(
        workbook_body(
            manifest,
            analysis,
            compiled_assets,
            table_sources,
            instrumentation_sections,
        )
    )
    run_command(
        ["typst", "compile", str(workbook_typ.resolve()), str(workbook_pdf.resolve())],
        cwd=report_dir,
    )

    report_metadata = {
        "generated_at": datetime.now().astimezone().isoformat(),
        "report_dir": str(report_dir),
        "workbook_typ": str(workbook_typ),
        "workbook_pdf": str(workbook_pdf),
        "figure_tex": [str(path) for path in figure_sources],
        "figure_assets": [str(path) for path in compiled_assets],
        "table_tex": [str(path) for path in table_sources],
        **instrumentation_exports,
        **data_exports,
    }
    write_json(report_dir / "report_metadata.json", report_metadata)
    return report_metadata


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build a Typst workbook from benchmark results"
    )
    parser.add_argument(
        "--manifest", required=True, type=Path, help="Path to run manifest JSON"
    )
    parser.add_argument(
        "--run-dir", required=True, type=Path, help="Path to the run directory"
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    build_report(args.manifest, args.run_dir)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
