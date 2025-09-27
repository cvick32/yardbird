#!/usr/bin/env python3

import json
import argparse
from pathlib import Path
from dataclasses import dataclass
from typing import List, Tuple


@dataclass
class TikzPoint:
    x: float
    y: float
    label: str
    color: str = "blue"


def parse_benchmark_json(json_file: Path) -> Tuple[List[TikzPoint], dict]:
    """Parse benchmark JSON and extract points for plotting"""
    with open(json_file) as f:
        data = json.load(f)

    points = []
    metadata = data.get("metadata", {})

    # Group benchmarks by base example name to compare strategies
    benchmark_groups = {}
    for benchmark in data.get("benchmarks", []):
        example = benchmark["example"]
        # Extract base example name (remove config prefix)
        base_name = example.split("_", 1)[-1] if "_" in example else example

        if base_name not in benchmark_groups:
            benchmark_groups[base_name] = {}

        if benchmark["result"]:
            result = benchmark["result"][0]
            strategy = result["strategy"]
            benchmark_groups[base_name][strategy] = {
                "runtime": result["run_time"] / 1000.0,  # Convert to seconds
                "depth": result["depth"],
                "result_type": list(result["result"].keys())[0]
                if result["result"]
                else "unknown",
            }

    # Create points for runtime comparison
    for base_name, strategies in benchmark_groups.items():
        if "abstract" in strategies and "concrete" in strategies:
            abs_time = strategies["abstract"]["runtime"]
            con_time = strategies["concrete"]["runtime"]

            # Determine color based on which is faster
            color = "red" if abs_time < con_time else "blue"

            points.append(
                TikzPoint(
                    x=con_time,
                    y=abs_time,
                    label=base_name.replace("examples/", "").replace(".vmt", ""),
                    color=color,
                )
            )

    return points, metadata


def generate_tikz_scatter(
    points: List[TikzPoint], title: str = "Runtime Comparison"
) -> str:
    """Generate TikZ code for scatter plot"""
    if not points:
        return "% No data points to plot"

    # Find data bounds
    x_vals = [p.x for p in points]
    y_vals = [p.y for p in points]

    x_min, x_max = min(x_vals), max(x_vals)
    y_min, y_max = min(y_vals), max(y_vals)

    # Use log scale bounds
    x_min_log = max(0.001, x_min)
    y_min_log = max(0.001, y_min)
    x_max_log = max(x_max, x_min_log * 10)
    y_max_log = max(y_max, y_min_log * 10)

    tikz_code = f"""\\begin{{tikzpicture}}
\\begin{{loglogaxis}}[
    title={{{title}}},
    xlabel={{Z3 Runtime (s)}},
    ylabel={{Yardbird Runtime (s)}},
    xmin={x_min_log:.3f}, xmax={x_max_log:.3f},
    ymin={y_min_log:.3f}, ymax={y_max_log:.3f},
    grid=major,
    legend pos=outer north east,
    width=10cm,
    height=8cm
]

% Data points"""

    # Add data points
    red_points = [p for p in points if p.color == "red"]
    blue_points = [p for p in points if p.color == "blue"]

    if red_points:
        tikz_code += "\n\\addplot[only marks, mark=*, color=red] coordinates {\n"
        for point in red_points:
            tikz_code += f"    ({point.x:.6f}, {point.y:.6f})\n"
        tikz_code += "};\n\\addlegendentry{Yardbird Faster}"

    if blue_points:
        tikz_code += "\n\\addplot[only marks, mark=*, color=blue] coordinates {\n"
        for point in blue_points:
            tikz_code += f"    ({point.x:.6f}, {point.y:.6f})\n"
        tikz_code += "};\n\\addlegendentry{Z3 Faster}"

    # Add diagonal line (x=y)
    tikz_code += f"""
% Diagonal line (x=y)
\\addplot[dashed, color=black] coordinates {{
    ({x_min_log:.6f}, {y_min_log:.6f})
    ({x_max_log:.6f}, {y_max_log:.6f})
}};
\\addlegendentry{{x = y}}

\\end{{loglogaxis}}
\\end{{tikzpicture}}"""

    return tikz_code


def generate_tikz_table(points: List[TikzPoint], metadata: dict) -> str:
    """Generate TikZ/LaTeX table from benchmark data"""
    if not points:
        return "% No data to table"

    table_code = """\\begin{longtable}{lrrr}
\\caption{Benchmark Results} \\\\
\\toprule
Example & Z3 Runtime (s) & Yardbird Runtime (s) & Speedup \\\\
\\midrule
\\endfirsthead
\\multicolumn{4}{c}{\\tablename\\ \\thetable\\ -- continued from previous page} \\\\
\\toprule
Example & Z3 Runtime (s) & Yardbird Runtime (s) & Speedup \\\\
\\midrule
\\endhead
\\midrule
\\multicolumn{4}{r}{Continued on next page} \\\\
\\endfoot
\\bottomrule
\\endlastfoot
"""

    # Sort points by example name
    sorted_points = sorted(points, key=lambda p: p.label)

    for point in sorted_points:
        speedup = point.x / point.y if point.y > 0 else float("inf")
        speedup_str = f"{speedup:.2f}x" if speedup != float("inf") else "∞"

        table_code += (
            f"{point.label} & {point.x:.3f} & {point.y:.3f} & {speedup_str} \\\\\n"
        )

    table_code += "\\end{longtable}"

    return table_code


def main():
    parser = argparse.ArgumentParser(
        description="Generate TikZ code from benchmark JSON"
    )
    parser.add_argument("json_file", help="Benchmark results JSON file")
    parser.add_argument(
        "--output-dir", help="Output directory for TikZ files", default="."
    )
    parser.add_argument("--scatter", action="store_true", help="Generate scatter plot")
    parser.add_argument("--table", action="store_true", help="Generate data table")
    parser.add_argument("--all", action="store_true", help="Generate all graphics")

    args = parser.parse_args()

    if not args.scatter and not args.table and not args.all:
        args.all = True

    json_file = Path(args.json_file)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(exist_ok=True)

    points, metadata = parse_benchmark_json(json_file)

    if args.scatter or args.all:
        tikz_scatter = generate_tikz_scatter(points, "Runtime Comparison")
        scatter_file = output_dir / "runtime_scatter.tikz"
        with open(scatter_file, "w") as f:
            f.write(tikz_scatter)
        print(f"Generated scatter plot: {scatter_file}")

    if args.table or args.all:
        tikz_table = generate_tikz_table(points, metadata)
        table_file = output_dir / "results_table.tikz"
        with open(table_file, "w") as f:
            f.write(tikz_table)
        print(f"Generated table: {table_file}")


if __name__ == "__main__":
    main()
