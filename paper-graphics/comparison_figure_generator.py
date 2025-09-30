#!/usr/bin/env python3

import json
import argparse
from pathlib import Path
from dataclasses import dataclass
from typing import List, Dict, Optional


# Constants for axiom instantiation counting (from main.py)
CONCRETE_ARRAY_Z3_STATS = ["array ax1", "array ax2"]

ABSTRACT_BETTER_COLOR = "orange"  # Orange for abstract better
Z3_BETTER_COLOR = "cyan!50!blue"  # Teal/cyan for Z3 better
EQUAL_COLOR = "black"


@dataclass
class BenchmarkResult:
    """Represents a single benchmark result with strategy outcomes"""

    example_name: str
    strategy: str
    cost_function: Optional[str]
    runtime_ms: float
    depth: int
    result_type: str  # "Success", "Timeout", "Error", "Panic", "NoProgress"
    success: bool
    found_proof: bool
    counterexample: bool
    used_instances: List[str]
    solver_stats: Dict

    def get_runtime(self):
        if self.result_type == "Success":
            return self.runtime_ms
        else:
            return 60000


@dataclass
class TikzPoint:
    """Point for TikZ plotting"""

    x: float
    y: float
    label: str
    color: str = Z3_BETTER_COLOR


class BenchmarkParser:
    """Parser for benchmark JSON results"""

    def __init__(self, json_paths: List[Path]):
        self.all_results = []
        self.metadata = {}

        for json_path in json_paths:
            with open(json_path) as f:
                data = json.load(f)

            # Store metadata from first file
            if not self.metadata:
                self.metadata = data.get("metadata", {})

            # Parse all benchmarks from this file
            for benchmark in data.get("benchmarks", []):
                example_full = benchmark["example"]
                example_name = self._extract_clean_example_name(example_full)

                for result_entry in benchmark.get("result", []):
                    result = self._parse_single_result(example_name, result_entry)
                    if result:
                        self.all_results.append(result)

    def get_metadata(self) -> Dict:
        """Get benchmark metadata"""
        return self.metadata

    def parse_benchmark_results(self) -> List[BenchmarkResult]:
        """Parse all benchmark results into structured data"""
        return self.all_results

    def _extract_clean_example_name(self, full_name: str) -> str:
        """Extract clean example name from full config-prefixed name"""
        # Pattern: config_prefix_examples/path/file.vmt
        # We want: examples/path/file.vmt
        if "_examples/" in full_name:
            return "examples/" + full_name.split("_examples/", 1)[1]
        return full_name

    def _parse_single_result(
        self, example_name: str, result_entry: Dict
    ) -> Optional[BenchmarkResult]:
        """Parse a single strategy result"""
        strategy = result_entry.get("strategy", "unknown")
        cost_function = result_entry.get("cost_function")
        runtime_ms = result_entry.get("run_time", 0)
        depth = result_entry.get("depth", 0)

        result_data = result_entry.get("result", {})

        # Determine result type and extract details
        result_type = list(result_data.keys())[0] if result_data else "Unknown"

        if result_type == "Success":
            success_data = result_data["Success"]
            return BenchmarkResult(
                example_name=example_name,
                strategy=strategy,
                cost_function=cost_function,
                runtime_ms=runtime_ms,
                depth=depth,
                result_type=result_type,
                success=True,
                found_proof=success_data.get("found_proof", False),
                counterexample=success_data.get("counterexample", False),
                used_instances=success_data.get("used_instances", []),
                solver_stats=success_data.get("solver_statistics", {}).get("stats", {}),
            )
        elif result_type == "Timeout":
            timeout_ms = result_data["Timeout"]
            return BenchmarkResult(
                example_name=example_name,
                strategy=strategy,
                cost_function=cost_function,
                runtime_ms=timeout_ms,
                depth=depth,
                result_type=result_type,
                success=False,
                found_proof=False,
                counterexample=False,
                used_instances=[],
                solver_stats={},
            )
        else:
            # Error, Panic, NoProgress
            return BenchmarkResult(
                example_name=example_name,
                strategy=strategy,
                cost_function=cost_function,
                runtime_ms=runtime_ms,
                depth=depth,
                result_type=result_type,
                success=False,
                found_proof=False,
                counterexample=False,
                used_instances=[],
                solver_stats={},
            )

    def get_runtime_comparison_points(
        self,
        strategy1: str = "concrete",
        strategy2: str = "abstract",
        cost_function: str = None,
    ) -> List[TikzPoint]:
        """Generate points for runtime comparison between two strategies"""
        results = self.parse_benchmark_results()

        # Group by example name and strategy key (strategy + cost_function for abstract)
        grouped: dict[str, BenchmarkResult] = {}
        for result in results:
            if result.example_name not in grouped:
                grouped[result.example_name] = {}

            # Create strategy key that includes cost function for abstract strategy
            if result.strategy == "abstract" and result.cost_function:
                strategy_key = f"{result.strategy}_{result.cost_function}"
            else:
                strategy_key = result.strategy

            grouped[result.example_name][strategy_key] = result

        if strategy2 == "abstract" and cost_function:
            strategy2_key = f"abstract_{cost_function}"
        else:
            strategy2_key = strategy2

        points = []
        for example_name, strategies in grouped.items():
            if strategy1 in strategies and strategy2_key in strategies:
                result1 = strategies[strategy1]
                result2 = strategies[strategy2_key]

                time1 = result1.get_runtime()
                time2 = result2.get_runtime()

                # Determine color based on which is faster
                if time2 < time1:
                    color = ABSTRACT_BETTER_COLOR
                elif time2 > time1:
                    color = Z3_BETTER_COLOR
                else:
                    color = EQUAL_COLOR
                # Clean up label
                label = example_name.replace("examples/", "").replace(".vmt", "")

                points.append(TikzPoint(x=time1, y=time2, label=label, color=color))

        return points

    def get_all_comparison_data(
        self,
        strategy1: str = "concrete",
        strategy2: str = "abstract",
        cost_function: str = None,
    ) -> List[tuple]:
        """Get all benchmark comparison data including unsuccessful results"""
        results = self.parse_benchmark_results()

        # Group by example name and strategy key (strategy + cost_function for abstract)
        grouped = {}
        for result in results:
            if result.example_name not in grouped:
                grouped[result.example_name] = {}

            # Create strategy key that includes cost function for abstract strategy
            if result.strategy == "abstract" and result.cost_function:
                strategy_key = f"{result.strategy}_{result.cost_function}"
            else:
                strategy_key = result.strategy

            grouped[result.example_name][strategy_key] = result

        # Determine strategy2 key based on cost function filter
        if strategy2 == "abstract" and cost_function:
            strategy2_key = f"abstract_{cost_function}"
        else:
            strategy2_key = strategy2

        comparison_data = []
        for example_name, strategies in grouped.items():
            if strategy1 in strategies and strategy2_key in strategies:
                result1 = strategies[strategy1]
                result2 = strategies[strategy2_key]

                # Clean up label
                label = example_name.replace("examples/", "").replace(".vmt", "")

                comparison_data.append((label, result1, result2))

        return comparison_data


def compute_axiom_instantiations(result: BenchmarkResult, bmc_depth: int) -> int:
    """Compute axiom instantiations for a benchmark result"""
    if not result.success:
        return 10000000  # Large penalty for unsuccessful results

    if result.strategy == "abstract":
        # Abstract: used_instances * BMC_DEPTH
        return len(result.used_instances) * bmc_depth

    elif result.strategy == "concrete":
        # Concrete: sum of concrete Z3 array axiom stats
        concrete_z3_count = 0
        for stat in CONCRETE_ARRAY_Z3_STATS:
            try:
                concrete_z3_count += int(result.solver_stats.get(stat, 0))
            except (ValueError, TypeError):
                pass

        return concrete_z3_count

    else:
        return 10000000  # Unknown strategy


def get_instantiation_comparison_points(
    parser_obj,
    strategy1: str = "concrete",
    strategy2: str = "abstract",
    cost_function: str = None,
    bmc_depth: int = 50,
) -> List[TikzPoint]:
    """Generate points for axiom instantiation comparison between two strategies"""
    results = parser_obj.parse_benchmark_results()

    # Group by example name and strategy key (strategy + cost_function for abstract)
    grouped: dict[str, BenchmarkResult] = {}
    for result in results:
        if result.example_name not in grouped:
            grouped[result.example_name] = {}

        # Create strategy key that includes cost function for abstract strategy
        if result.strategy == "abstract" and result.cost_function:
            strategy_key = f"{result.strategy}_{result.cost_function}"
        else:
            strategy_key = result.strategy

        grouped[result.example_name][strategy_key] = result

    # Determine strategy2 key based on cost function filter
    if strategy2 == "abstract" and cost_function:
        strategy2_key = f"abstract_{cost_function}"
    else:
        strategy2_key = strategy2

    points = []
    for example_name, strategies in grouped.items():
        if strategy1 in strategies and strategy2_key in strategies:
            result1 = strategies[strategy1]
            result2 = strategies[strategy2_key]

            inst1 = compute_axiom_instantiations(result1, bmc_depth)
            inst2 = compute_axiom_instantiations(result2, bmc_depth)

            # Determine color based on which has fewer instantiations
            if inst2 < inst1:
                color = ABSTRACT_BETTER_COLOR
            elif inst2 > inst1:
                color = Z3_BETTER_COLOR
            else:
                color = EQUAL_COLOR

            # Clean up label
            label = example_name.replace("examples/", "").replace(".vmt", "")

            points.append(TikzPoint(x=inst1, y=inst2, label=label, color=color))

    return points


def print_instantiation_statistics(
    points: List[TikzPoint], strategy1: str = "concrete", strategy2: str = "abstract"
):
    """Print detailed instantiation comparison statistics between two strategies"""
    if not points:
        print("No comparable benchmark pairs found for instantiation analysis.")
        return

    # Count wins
    strategy2_fewer = sum(
        1 for p in points if p.color == ABSTRACT_BETTER_COLOR
    )  # y < x means strategy2 fewer
    strategy1_fewer = sum(
        1 for p in points if p.color == Z3_BETTER_COLOR
    )  # x < y means strategy1 fewer
    ties = len(points) - strategy2_fewer - strategy1_fewer

    # Instantiation statistics
    strategy1_insts = [p.x for p in points]
    strategy2_insts = [p.y for p in points]

    def compute_stats(values):
        import statistics

        return {
            "mean": statistics.mean(values),
            "median": statistics.median(values),
            "min": min(values),
            "max": max(values),
            "stdev": statistics.stdev(values) if len(values) > 1 else 0,
        }

    stats1 = compute_stats(strategy1_insts)
    stats2 = compute_stats(strategy2_insts)

    # Reduction analysis
    reductions = []
    for p in points:
        if p.y > 0:
            reduction = (
                p.x / p.y
            )  # how much fewer instantiations strategy2 has compared to strategy1
            reductions.append(reduction)
        elif p.x > 0:
            # If strategy2 has 0 but strategy1 has some, that's infinite reduction
            reductions.append(float("inf"))

    # Filter out infinite values for stats computation
    finite_reductions = [r for r in reductions if r != float("inf")]
    reduction_stats = compute_stats(finite_reductions) if finite_reductions else None
    infinite_reductions = len(reductions) - len(finite_reductions)

    print("\n=== Axiom Instantiation Comparison Statistics ===")
    print(f"Total comparable benchmarks: {len(points)}")
    print(
        f"{strategy2.title()} fewer instantiations: {strategy2_fewer} ({strategy2_fewer / len(points) * 100:.1f}%)"
    )
    print(
        f"{strategy1.title()} fewer instantiations: {strategy1_fewer} ({strategy1_fewer / len(points) * 100:.1f}%)"
    )
    if ties > 0:
        print(f"Ties: {ties} ({ties / len(points) * 100:.1f}%)")

    print("\n=== Instantiation Statistics ===")
    print(f"{strategy1.title()} Strategy:")
    print(f"  Mean: {stats1['mean']:.0f}")
    print(f"  Median: {stats1['median']:.0f}")
    print(f"  Min: {stats1['min']:.0f}")
    print(f"  Max: {stats1['max']:.0f}")
    print(f"  StdDev: {stats1['stdev']:.0f}")

    print(f"\n{strategy2.title()} Strategy:")
    print(f"  Mean: {stats2['mean']:.0f}")
    print(f"  Median: {stats2['median']:.0f}")
    print(f"  Min: {stats2['min']:.0f}")
    print(f"  Max: {stats2['max']:.0f}")
    print(f"  StdDev: {stats2['stdev']:.0f}")

    if reduction_stats or infinite_reductions > 0:
        print(
            f"\n=== Instantiation Reduction Analysis ({strategy1} count / {strategy2} count) ==="
        )
        if infinite_reductions > 0:
            print(f"  Infinite reductions (strategy2 has 0): {infinite_reductions}")
        if reduction_stats:
            print(f"  Mean reduction: {reduction_stats['mean']:.2f}x")
            print(f"  Median reduction: {reduction_stats['median']:.2f}x")
            print(f"  Best reduction: {reduction_stats['max']:.2f}x")
            print(f"  Worst reduction: {reduction_stats['min']:.2f}x")

        # Additional analysis
        significant_reductions = (
            sum(1 for r in finite_reductions if r > 2.0) + infinite_reductions
        )
        significant_increases = sum(1 for r in finite_reductions if r < 0.5)

        print("\n=== Instantiation Categories ===")
        print(
            f"Significant reductions (>2x fewer): {significant_reductions} ({significant_reductions / len(reductions) * 100:.1f}%)"
        )
        print(
            f"Significant increases (<0.5x fewer): {significant_increases} ({significant_increases / len(reductions) * 100:.1f}%)"
        )
        print(
            f"Similar instantiation count (0.5x-2x): {len(reductions) - significant_reductions - significant_increases} ({(len(reductions) - significant_reductions - significant_increases) / len(reductions) * 100:.1f}%)"
        )


def print_comparison_statistics(
    points: List[TikzPoint], strategy1: str = "concrete", strategy2: str = "abstract"
):
    """Print detailed comparison statistics between two strategies"""
    if not points:
        print("No comparable benchmark pairs found.")
        return

    # Count wins
    strategy2_faster = sum(
        1 for p in points if p.color == ABSTRACT_BETTER_COLOR
    )  # y < x means strategy2 faster
    strategy1_faster = sum(
        1 for p in points if p.color == Z3_BETTER_COLOR
    )  # x < y means strategy1 faster
    ties = len(points) - strategy2_faster - strategy1_faster

    # Runtime statistics
    strategy1_times = [p.x for p in points]
    strategy2_times = [p.y for p in points]

    def compute_stats(times):
        import statistics

        return {
            "mean": statistics.mean(times),
            "median": statistics.median(times),
            "min": min(times),
            "max": max(times),
            "stdev": statistics.stdev(times) if len(times) > 1 else 0,
        }

    stats1 = compute_stats(strategy1_times)
    stats2 = compute_stats(strategy2_times)

    # Speedup analysis
    speedups = []
    for p in points:
        if p.y > 0:
            speedup = p.x / p.y  # how much faster strategy2 is compared to strategy1
            speedups.append(speedup)

    speedup_stats = compute_stats(speedups) if speedups else None

    print("\n=== Benchmark Comparison Statistics ===")
    print(f"Total comparable benchmarks: {len(points)}")
    print(
        f"{strategy2.title()} wins: {strategy2_faster} ({strategy2_faster / len(points) * 100:.1f}%)"
    )
    print(
        f"{strategy1.title()} wins: {strategy1_faster} ({strategy1_faster / len(points) * 100:.1f}%)"
    )
    if ties > 0:
        print(f"Ties: {ties} ({ties / len(points) * 100:.1f}%)")

    print("\n=== Runtime Statistics (seconds) ===")
    print(f"{strategy1.title()} Strategy:")
    print(f"  Mean: {stats1['mean']:.3f}s")
    print(f"  Median: {stats1['median']:.3f}s")
    print(f"  Min: {stats1['min']:.3f}s")
    print(f"  Max: {stats1['max']:.3f}s")
    print(f"  StdDev: {stats1['stdev']:.3f}s")

    print(f"\n{strategy2.title()} Strategy:")
    print(f"  Mean: {stats2['mean']:.3f}s")
    print(f"  Median: {stats2['median']:.3f}s")
    print(f"  Min: {stats2['min']:.3f}s")
    print(f"  Max: {stats2['max']:.3f}s")
    print(f"  StdDev: {stats2['stdev']:.3f}s")

    if speedup_stats:
        print(f"\n=== Speedup Analysis ({strategy1} time / {strategy2} time) ===")
        print(f"  Mean speedup: {speedup_stats['mean']:.2f}x")
        print(f"  Median speedup: {speedup_stats['median']:.2f}x")
        print(f"  Best speedup: {speedup_stats['max']:.2f}x")
        print(f"  Worst speedup: {speedup_stats['min']:.2f}x")

        # Additional analysis
        significant_speedups = sum(1 for s in speedups if s > 2.0)
        significant_slowdowns = sum(1 for s in speedups if s < 0.5)

        print("\n=== Performance Categories ===")
        print(
            f"Significant speedups (>2x): {significant_speedups} ({significant_speedups / len(speedups) * 100:.1f}%)"
        )
        print(
            f"Significant slowdowns (<0.5x): {significant_slowdowns} ({significant_slowdowns / len(speedups) * 100:.1f}%)"
        )
        print(
            f"Similar performance (0.5x-2x): {len(speedups) - significant_speedups - significant_slowdowns} ({(len(speedups) - significant_speedups - significant_slowdowns) / len(speedups) * 100:.1f}%)"
        )


def print_comparison_table(
    comparison_data: List[tuple],
    strategy1: str = "concrete",
    strategy2: str = "abstract",
):
    """Print a human-readable table of all benchmark comparisons"""
    if not comparison_data:
        print("No comparison data found.")
        return

    print("\n=== Detailed Benchmark Comparison Table ===")
    print(f"{'Benchmark':<40} {strategy1.title():<20} {strategy2.title():<20}")
    print(f"{'=' * 40} {'=' * 20} {'=' * 20}")

    for label, result1, result2 in sorted(comparison_data):
        # Format result info
        def format_result(result):
            if result.success:
                runtime_s = result.runtime_ms / 1000.0
                return f"(Success, {runtime_s:.3f}s)"
            else:
                runtime_s = result.runtime_ms / 1000.0
                return f"({result.result_type}, {runtime_s:.3f}s)"

        result1_str = format_result(result1)
        result2_str = format_result(result2)

        # Truncate label if too long
        display_label = label if len(label) <= 39 else label[:36] + "..."

        print(f"{display_label:<40} {result1_str:<20} {result2_str:<20}")

    # Summary statistics
    total = len(comparison_data)
    both_success = sum(1 for _, r1, r2 in comparison_data if r1.success and r2.success)
    strategy1_only = sum(
        1 for _, r1, r2 in comparison_data if r1.success and not r2.success
    )
    strategy2_only = sum(
        1 for _, r1, r2 in comparison_data if not r1.success and r2.success
    )
    both_fail = sum(
        1 for _, r1, r2 in comparison_data if not r1.success and not r2.success
    )

    print("\n=== Success Rate Summary ===")
    print(
        f"Both strategies succeed: {both_success}/{total} ({both_success / total * 100:.1f}%)"
    )
    print(
        f"Only {strategy1} succeeds: {strategy1_only}/{total} ({strategy1_only / total * 100:.1f}%)"
    )
    print(
        f"Only {strategy2} succeeds: {strategy2_only}/{total} ({strategy2_only / total * 100:.1f}%)"
    )
    print(f"Both strategies fail: {both_fail}/{total} ({both_fail / total * 100:.1f}%)")


class TikzGenerator:
    """Generate TikZ code from benchmark data"""

    @staticmethod
    def generate_scatter_plot(
        points: List[TikzPoint],
        title: str = "Runtime Comparison",
        xlabel: str = "Concrete Strategy Runtime (s)",
        ylabel: str = "Abstract Strategy Runtime (s)",
        caption: str = None,
    ) -> str:
        """Generate TikZ scatter plot code"""
        if not points:
            return "% No data points to plot"

        # Find data bounds
        x_vals = [p.x for p in points]
        y_vals = [p.y for p in points]

        x_min, x_max = min(x_vals), max(x_vals)
        y_min, y_max = min(y_vals), max(y_vals)

        # Use log scale bounds with safety margins
        x_min_log = max(0.001, x_min * 0.5)
        y_min_log = max(0.001, y_min * 0.5)
        x_max_log = max(x_max * 2, x_min_log * 10)
        y_max_log = max(y_max * 2, y_min_log * 10)

        tikz_code = f"""\\begin{{figure}}[htbp]
\\centering
\\begin{{tikzpicture}}
\\begin{{loglogaxis}}[
    title={{{title}}},
    xlabel={{{xlabel}}},
    ylabel={{{ylabel}}},
    xmin={x_min_log:.3f}, xmax={x_max_log:.3f},
    ymin={y_min_log:.3f}, ymax={y_max_log:.3f},
    grid=major,
    width=\\columnwidth,
    height=8cm
]

% Data points"""

        # Group points by color
        abs_points = [p for p in points if p.color == ABSTRACT_BETTER_COLOR]
        z3_points = [p for p in points if p.color == Z3_BETTER_COLOR]
        equal_points = [p for p in points if p.color == EQUAL_COLOR]

        if abs_points:
            tikz_code += f"\n\\addplot[only marks, mark=*, color={ABSTRACT_BETTER_COLOR}] coordinates {{\n"
            for point in abs_points:
                tikz_code += f"    ({point.x:.6f}, {point.y:.6f})\n"
            tikz_code += "};\n"

        if z3_points:
            tikz_code += f"\n\\addplot[only marks, mark=*, color={Z3_BETTER_COLOR}] coordinates {{\n"
            for point in z3_points:
                tikz_code += f"    ({point.x:.6f}, {point.y:.6f})\n"
            tikz_code += "};\n"

        if equal_points:
            tikz_code += (
                f"\n\\addplot[only marks, mark=*, color={EQUAL_COLOR}] coordinates {{\n"
            )
            for point in equal_points:
                tikz_code += f"    ({point.x:.6f}, {point.y:.6f})\n"
            tikz_code += "};\n"

        # Add diagonal line (x=y)
        tikz_code += f"""
% Diagonal line (x=y)
\\addplot[dashed, color=black] coordinates {{
    ({x_min_log:.6f}, {y_min_log:.6f})
    ({x_max_log:.6f}, {y_max_log:.6f})
}};
\\end{{loglogaxis}}
\\end{{tikzpicture}}"""

        # Add caption if provided
        if caption:
            tikz_code += f"\n\\caption{{{caption}}}"

        tikz_code += "\n\\end{figure}"

        return tikz_code

    @staticmethod
    def generate_table(
        points: List[TikzPoint], title: str = "Benchmark Results"
    ) -> str:
        """Generate LaTeX table from benchmark data"""
        if not points:
            return "% No data to table"

        table_code = f"""% Required packages: \\usepackage{{longtable}} \\usepackage{{booktabs}}
\\begin{{longtable}}{{lrrr}}
\\caption{{{title}}} \\\\
\\toprule
Example & Concrete Runtime (s) & Abstract Runtime (s) & Speedup \\\\
\\midrule
\\endfirsthead
\\multicolumn{{4}}{{c}}{{\\tablename\\ \\thetable\\ -- continued from previous page}} \\\\
\\toprule
Example & Concrete Runtime (s) & Abstract Runtime (s) & Speedup \\\\
\\midrule
\\endhead
\\midrule
\\multicolumn{{4}}{{r}}{{Continued on next page}} \\\\
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
    parser.add_argument("json_files", nargs="+", help="Benchmark results JSON file(s)")
    parser.add_argument(
        "--output-dir", help="Output directory for TikZ files", default="."
    )
    parser.add_argument("--scatter", action="store_true", help="Generate scatter plot")
    parser.add_argument(
        "--tikz-table", action="store_true", help="Generate LaTeX table"
    )
    parser.add_argument(
        "--table", action="store_true", help="Print human-readable comparison table"
    )
    parser.add_argument("--all", action="store_true", help="Generate all graphics")
    parser.add_argument(
        "--instantiations",
        action="store_true",
        help="Compute axiom instantiation statistics",
    )
    parser.add_argument(
        "--bmc-depth",
        type=int,
        default=50,
        help="BMC depth for instantiation calculation",
    )

    args = parser.parse_args()

    if not args.scatter and not args.tikz_table and not args.table and not args.all:
        args.all = True

    json_files = [Path(f) for f in args.json_files]
    output_dir = Path(args.output_dir)
    output_dir.mkdir(exist_ok=True)

    # Parse benchmark data
    parser_obj = BenchmarkParser(json_files)
    metadata = parser_obj.get_metadata()

    print(f"Parsed benchmark data from {metadata.get('timestamp', 'unknown time')}")
    print(f"Config: {metadata.get('config_name', 'unknown')}")
    print(f"Total benchmarks: {metadata.get('total_benchmarks', 'unknown')}")

    # Show available strategies
    results = parser_obj.parse_benchmark_results()
    strategies = set(r.strategy for r in results)
    print(f"Available strategies: {strategies}")
    print(f"Total parsed results: {len(results)}")

    # run comparison for both
    cost_functions = ["symbol-cost", "a-s-t-size"]
    for cost_func in cost_functions:
        if cost_func == "symbol-cost":
            cost_func_name = "BMC Cost"
        else:
            cost_func_name = "AST Size"
        print(f"\n{'=' * 60}")
        print(f"ANALYSIS FOR ABSTRACT STRATEGY WITH {cost_func.upper()}")
        print(f"{'=' * 60}")

        # Get comparison data for this cost function
        all_data = parser_obj.get_all_comparison_data("concrete", "abstract", cost_func)
        points = parser_obj.get_runtime_comparison_points(
            "concrete", "abstract", cost_func
        )

        print(f"Found {len(all_data)} total benchmark pairs")
        print(
            f"Found {len(points)} successful benchmark pairs for concrete vs abstract ({cost_func})"
        )

        # Print human-readable table if requested
        if args.table:
            print_comparison_table(all_data, "concrete", f"{'abstract'} ({cost_func})")

        # Print detailed statistics (only for successful comparisons)
        if points:
            print_comparison_statistics(
                points, "concrete", f"{'abstract'} ({cost_func})"
            )
        else:
            print("No successful benchmark pairs found for statistical analysis.")

        # Compute instantiation analysis if requested
        if args.instantiations:
            inst_points = get_instantiation_comparison_points(
                parser_obj,
                "concrete",
                "abstract",
                cost_func,
                args.bmc_depth,
            )
            if inst_points:
                print_instantiation_statistics(
                    inst_points, "concrete", f"{'abstract'} ({cost_func})"
                )
            else:
                print("No successful benchmark pairs found for instantiation analysis.")

        # Generate outputs with cost function suffix
        if args.scatter or args.all:
            title = f"Runtime Comparison ({cost_func_name} vs Z3)"
            xlabel = "Z3 Strategy Runtime (s)"
            ylabel = f"{cost_func_name} Runtime (s)"

            tikz_scatter = TikzGenerator.generate_scatter_plot(
                points,
                title,
                xlabel,
                ylabel,
                caption=f"Runtime comparison between {cost_func_name} and the built-in Z3 array theory.",
            )
            scatter_file = (
                output_dir / f"runtime_scatter_{cost_func.replace('-', '_')}.tikz"
            )
            with open(scatter_file, "w") as f:
                f.write(tikz_scatter)
            print(f"Generated scatter plot: {scatter_file}")

        # Generate instantiation scatter plot if requested
        if args.instantiations and (args.scatter or args.all):
            inst_points = get_instantiation_comparison_points(
                parser_obj,
                "concrete",
                "abstract",
                cost_func,
                args.bmc_depth,
            )
            if inst_points:
                title = f"Instantiation Comparison ({cost_func_name} vs Z3)"
                ylabel = f"{cost_func_name} Instantiations"
                xlabel = "Z3 Instantiations"

                tikz_scatter = TikzGenerator.generate_scatter_plot(
                    inst_points,
                    title,
                    xlabel,
                    ylabel,
                    caption=f"Comparison between the number of array axiom instantiations needed by {cost_func_name} and the built-in Z3 array theory.",
                )
                scatter_file = (
                    output_dir
                    / f"instantiation_scatter_{cost_func.replace('-', '_')}.tikz"
                )
                with open(scatter_file, "w") as f:
                    f.write(tikz_scatter)
                print(f"Generated instantiation scatter plot: {scatter_file}")
            else:
                print(
                    "No successful benchmark pairs found for instantiation scatter plot."
                )

        if args.tikz_table or args.all:
            table_title = f"Runtime Comparison Results {cost_func} ({metadata.get('config_name', 'Benchmark')})"
            tikz_table = TikzGenerator.generate_table(points, table_title)
            table_file = (
                output_dir / f"results_table_{cost_func.replace('-', '_')}.tikz"
            )
            with open(table_file, "w") as f:
                f.write(tikz_table)
            print(f"Generated LaTeX table: {table_file}")


if __name__ == "__main__":
    main()
