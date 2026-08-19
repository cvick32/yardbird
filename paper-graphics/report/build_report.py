#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
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
from report.instrumentation import build_instrumentation_report  # noqa: E402
from report.typst import typst_table  # noqa: E402


FIGURE_PREFIXES = (
    "runtime_scatter_",
    "instantiation_scatter_",
    "runtime_cactus_plot",
    "instantiation_cactus_plot",
    "conflict_cactus_plot",
    "solver_runtime_cactus_plot",
    "solver_stat_",
    "solver_boundary_",
)
GENERATED_TEX_PATTERNS = (
    "all_benchmarks_table.tex",
    "summary_statistics.tex",
    "shared_benchmark_analysis.tex",
    "runtime_*.tex",
    "instantiation_*.tex",
    "conflict_*.tex",
    "solver_runtime_*.tex",
    "solver_stat_*.tex",
    "solver_boundary_*.tex",
    "unique_solves_*.tex",
)

GENERATED_ASSET_PATTERNS = (
    "runtime_*.pdf",
    "instantiation_*.pdf",
    "conflict_*.pdf",
    "solver_runtime_*.pdf",
    "solver_stat_*.pdf",
    "solver_boundary_*.pdf",
    "runtime_*.png",
    "instantiation_*.png",
    "conflict_*.png",
    "solver_runtime_*.png",
    "solver_stat_*.png",
    "solver_boundary_*.png",
)


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


def is_figure_tex_path(path: Path) -> bool:
    return any(path.stem.startswith(prefix) for prefix in FIGURE_PREFIXES)


def has_renderable_latex(path: Path) -> bool:
    return any(
        line.strip() and not line.lstrip().startswith("%")
        for line in path.read_text().splitlines()
    )


def figure_tex_paths(tex_dir: Path) -> list[Path]:
    return [
        path
        for path in sorted(tex_dir.glob("*.tex"))
        if is_figure_tex_path(path) and has_renderable_latex(path)
    ]


def table_tex_paths(tex_dir: Path) -> list[Path]:
    return [
        path
        for path in sorted(tex_dir.glob("*.tex"))
        if not is_figure_tex_path(path)
    ]


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
    # Typst/Poppler can render overlapping PDF form resources incorrectly when
    # many independently compiled PGF plots share a workbook. Embed a high-DPI
    # raster while retaining the cropped PDF as a reusable report asset.
    output_png = assets_dir / f"{fragment_path.stem}.png"
    run_command(
        [
            "pdftoppm",
            "-png",
            "-r",
            "180",
            "-singlefile",
            str(output_pdf),
            str(output_png.with_suffix("")),
        ],
        cwd=assets_dir,
    )
    return output_png


def figure_title(fragment: Path) -> str:
    title = fragment.stem.replace("_", " ").strip()
    if title.startswith("instantiation scatter "):
        return "Instantiation Comparison"
    if title.startswith("runtime scatter "):
        return "Runtime Comparison"
    if title.startswith("solver boundary "):
        return "Z3 vs End-to-End Speedup"
    if title == "solver runtime cactus plot":
        return "Z3 Runtime Across Strategies"
    if title.startswith("solver stat "):
        metric = title.removeprefix("solver stat ").split(" abstract", 1)[0]
        return f"Paired Z3: {metric.title()}"
    return " ".join(word.capitalize() for word in title.split())


def short_benchmark_name(name: str) -> str:
    return name.removeprefix("examples/array/").removesuffix(".vmt")


def seconds(runtime_ms: int | float | None) -> str:
    if runtime_ms is None:
        return "-"
    return f"{runtime_ms / 1000.0:.3f}s"


def diagnostic_number(value: int | float | None) -> str:
    if value is None:
        return "-"
    if abs(value) >= 1000:
        return f"{value:,.0f}"
    return f"{value:g}"


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

    for diagnostic in analysis.get("solver_diagnostics", []):
        metric_rows = []
        for metric in diagnostic["metrics"]:
            ratio = metric["paired_median_ratio"]
            correlation = metric["paired_log_ratio_solver_time_spearman"]
            metric_rows.append(
                [
                    metric["label"],
                    diagnostic_number(metric["candidate_median"]),
                    diagnostic_number(metric["baseline_median"]),
                    f"{ratio:.3f}x" if ratio is not None else "-",
                    f"{metric['candidate_lower_count']} / {metric['equal_count']} / "
                    f"{metric['candidate_higher_count']}",
                    f"{correlation:.3f}" if correlation is not None else "-",
                ]
            )
        lines.extend(
            [
                "#pagebreak()",
                "",
                f"= Paired Z3 Diagnostics: {diagnostic['candidate_display_name']} vs "
                f"{diagnostic['baseline_display_name']}",
                "",
                f"These counters compare the *{diagnostic['shared_solved_count']} benchmarks* "
                "solved by both strategies. This paired view avoids the differing-population "
                "effect in the cactus curves.",
                "",
                typst_table(
                    [
                        "Counter",
                        "Candidate",
                        "Baseline",
                        "C/B ratio",
                        "C lower/= /higher",
                        "rho time",
                    ],
                    metric_rows,
                    columns="(1.45fr, .75fr, .75fr, .7fr, 1fr, .65fr)",
                ),
                "",
                "The ratio is the median of positive per-benchmark candidate/baseline "
                "ratios. _rho time_ is Spearman correlation between the log1p counter "
                "difference "
                "and log solver-time ratio; it measures association, not causal cost.",
                "",
            ]
        )
        conflict_metric = next(
            (
                metric
                for metric in diagnostic["metrics"]
                if metric["stat_key"] == "conflicts"
            ),
            None,
        )
        if conflict_metric is not None:
            lines.extend(
                [
                    "Among candidate end-to-end runtime wins, candidate conflicts were "
                    f"lower / equal / higher in *{conflict_metric['runtime_win_candidate_lower_count']} / "
                    f"{conflict_metric['runtime_win_equal_count']} / "
                    f"{conflict_metric['runtime_win_candidate_higher_count']}* cases.",
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
            rows = comparison[key][:7]
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
            "- `data/solver_diagnostics.csv`: paired Z3 counter summaries and correlations",
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
    (report_dir / "template.typ").write_text(TEMPLATE_PATH.read_text())

    json_files = [Path(subrun["result_path"]) for subrun in manifest["subruns"]]
    grouped, strategy_keys, all_results = benchmark_groupings(json_files)
    baseline_strategy = choose_baseline_strategy(strategy_keys)
    if baseline_strategy is None:
        raise RuntimeError("No benchmark strategies were found in the run artifacts")
    analysis = build_analysis(grouped, strategy_keys, baseline_strategy)
    data_exports = write_analysis_exports(report_dir, analysis)
    instrumentation_report = build_instrumentation_report(manifest, report_dir)
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
            instrumentation_report.sections,
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
        **instrumentation_report.exports,
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
