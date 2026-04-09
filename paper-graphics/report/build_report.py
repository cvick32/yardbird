#!/usr/bin/env python3

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parents[2]
PAPER_GRAPHICS_ROOT = PROJECT_ROOT / "paper-graphics"
TEMPLATE_PATH = PAPER_GRAPHICS_ROOT / "report" / "template.typ"
sys.path.insert(0, str(PAPER_GRAPHICS_ROOT))

from main import generate_figures  # noqa: E402
from src.benchmark_parsing import BenchmarkParser  # noqa: E402


FIGURE_PREFIXES = (
    "runtime_scatter_",
    "instantiation_scatter_",
    "runtime_cactus_plot",
    "instantiation_cactus_plot",
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
        if result.strategy == "abstract" and result.cost_function:
            strategy_key = f"{result.strategy}_{result.cost_function}"
        else:
            strategy_key = result.strategy
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
\begin{{document}}
\input{{{fragment}}}
\end{{document}}
"""


def compile_figure_fragment(fragment_path: Path, assets_dir: Path) -> Path:
    assets_dir.mkdir(parents=True, exist_ok=True)
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
        for suffix in (".aux", ".log", ".out"):
            temp_artifact = assets_dir / f"wrapper{suffix}"
            if temp_artifact.exists():
                temp_artifact.unlink()
    return output_pdf


def figure_title(fragment: Path) -> str:
    title = fragment.stem.replace("_", " ").strip()
    return " ".join(word.capitalize() for word in title.split())


def workbook_body(
    manifest: dict, figure_assets: list[Path], table_sources: list[Path]
) -> str:
    benchmark_types = ", ".join(manifest.get("benchmark_types", []))
    lines = [
        '#import "template.typ": *',
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

    for asset in figure_assets:
        rel_asset = asset.relative_to(asset.parent.parent).as_posix()
        lines.extend(
            [
                "#pagebreak()",
                "",
                f"= {figure_title(asset)}",
                "",
                f'#figure(image("{rel_asset}", width: 100%), caption: [{figure_title(asset)}])',
                "",
            ]
        )

    lines.extend(["#pagebreak()", "", "= Generated Tables", ""])
    if table_sources:
        lines.append(
            "The following LaTeX/TikZ tables were generated alongside the workbook and are available in the report directory:"
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
    (report_dir / "template.typ").write_text(TEMPLATE_PATH.read_text())

    json_files = [Path(subrun["result_path"]) for subrun in manifest["subruns"]]
    grouped, strategy_keys, all_results = benchmark_groupings(json_files)
    generate_figures(grouped, strategy_keys, all_results, tex_dir)

    figure_sources = figure_tex_paths(tex_dir)
    table_sources = table_tex_paths(tex_dir)
    compiled_assets = [
        compile_figure_fragment(path, assets_dir) for path in figure_sources
    ]

    workbook_typ = report_dir / "workbook.typ"
    workbook_pdf = report_dir / "workbook.pdf"
    workbook_typ.write_text(workbook_body(manifest, compiled_assets, table_sources))
    run_command(
        ["typst", "compile", str(workbook_typ), str(workbook_pdf)], cwd=report_dir
    )

    report_metadata = {
        "generated_at": manifest.get("updated_at"),
        "report_dir": str(report_dir),
        "workbook_typ": str(workbook_typ),
        "workbook_pdf": str(workbook_pdf),
        "figure_tex": [str(path) for path in figure_sources],
        "figure_assets": [str(path) for path in compiled_assets],
        "table_tex": [str(path) for path in table_sources],
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
