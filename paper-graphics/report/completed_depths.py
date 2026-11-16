"""Completed BMC depth plots, including partial progress from timed-out runs."""

import csv
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from report.protocol_depths import depth_cell
from report.typst import typst_cell


def completed_depth(result):
    """None means unavailable; -1 means recorded progress with no completed check."""
    progress = result.run_progress if result else None
    if not isinstance(progress, dict) or "deepest_completed_depth" not in progress:
        return None
    value = progress["deepest_completed_depth"]
    return -1 if value is None else value


def generate_depth_report(grouped, labels, report_dir: Path):
    benchmarks = sorted(name for name in grouped if name.lower().endswith(".vmt"))
    if not benchmarks:
        return [], {}
    keys = list(labels)
    data_dir = report_dir / "data"
    data_dir.mkdir(exist_ok=True)
    csv_path = data_dir / "completed_depths.csv"
    with csv_path.open("w", newline="") as stream:
        writer = csv.writer(stream)
        writer.writerow(["benchmark", "strategy", "strategy_id", "completed_depth",
                         "progress_available", "current_depth", "target_depth", "outcome"])
        for name in benchmarks:
            for key in keys:
                result = grouped[name].get(key)
                progress = (result.run_progress or {}) if result else {}
                depth = completed_depth(result)
                writer.writerow([name, labels[key], key, "" if depth is None else depth,
                                 depth is not None, progress.get("current_depth"),
                                 progress.get("target_depth"), depth_cell(result)])
    depths = [completed_depth(r) for name in benchmarks for r in grouped[name].values()]
    maximum = max([d for d in depths if d is not None] + [0])
    sections = []
    assets = []
    # Split large matrices so labels and annotations remain readable in the workbook.
    for column_start in range(0, len(keys), 16):
        page_keys = keys[column_start:column_start + 16]
        for row_start in range(0, len(benchmarks), 24):
            page_names = benchmarks[row_start:row_start + 24]
            values = np.full((len(page_names), len(page_keys)), np.nan)
            for i, name in enumerate(page_names):
                for j, key in enumerate(page_keys):
                    depth = completed_depth(grouped[name].get(key))
                    if depth is not None:
                        values[i, j] = depth
            fig, ax = plt.subplots(figsize=(13, 2.6 + .34 * len(page_names)))
            cmap = plt.get_cmap("YlGnBu").copy()
            cmap.set_bad("#e5e7eb")
            im = ax.imshow(values, cmap=cmap, vmin=-1, vmax=max(1, maximum), aspect="auto")
            ax.set_xticks(range(len(page_keys)), [f"S{keys.index(k) + 1}" for k in page_keys])
            names = [name.split("generated-vmt/")[-1].removeprefix("examples/")
                     .removesuffix(".vmt") for name in page_names]
            ax.set_yticks(range(len(page_names)), names, fontsize=9)
            ax.tick_params(top=True, labeltop=True, bottom=False, labelbottom=False, length=0)
            for i, name in enumerate(page_names):
                for j, key in enumerate(page_keys):
                    result = grouped[name].get(key)
                    cell = depth_cell(result)
                    number, _, outcome = cell.partition(" (")
                    outcome = outcome.rstrip(")")
                    annotation = number if outcome == "OK" else f"{number}\n{outcome}"
                    ax.text(j, i, annotation, ha="center", va="center", fontsize=7,
                            color="white" if values[i, j] > maximum * .6 else "black")
            ax.set_title("Deepest completed BMC depth", pad=30)
            fig.colorbar(im, ax=ax, fraction=.025, pad=.025,
                         ticks=sorted({0, maximum // 2, maximum}),
                         label="Completed depth (zero-based)")
            fig.tight_layout()
            stem = f"completed_depths_{column_start // 16 + 1}_{row_start // 24 + 1}"
            for extension in ("png", "pdf"):
                path = report_dir / "assets" / f"{stem}.{extension}"
                fig.savefig(path, dpi=200, bbox_inches="tight")
                assets.append(str(path))
            plt.close(fig)
            sections.extend([
                "#pagebreak()", "= Completed BMC Depths", "",
                typst_cell("Largest completed depth, not the depth being attempted. Target 20 checks depths 0-19; "
                "completing the bound is not an unbounded proof. T = timeout; PROOF = proof; "
                "CEX/UNK@k = counterexample/unknown at k; ERR = failure. "
                "none = no completed check; ? = unavailable; missing = no result. "
                "Colors share one absolute depth scale across all panels.")[1:-1], "",
                f'#image("assets/{stem}.png", width: 100%)', "",
                '#text(size: 8pt)[',
            ])
            for key in page_keys:
                sections.extend([typst_cell(f"S{keys.index(key) + 1}: {labels[key]}")[1:-1], "#linebreak()"])
            sections.extend([
                "]", "", "Exact values and termination outcomes: `data/completed_depths.csv`.", "",
            ])
    return sections, {"completed_depth_csv": str(csv_path), "completed_depth_assets": assets}
