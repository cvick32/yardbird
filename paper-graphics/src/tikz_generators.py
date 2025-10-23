"""TikZ/LaTeX code generators for benchmark visualization"""

from typing import List, Dict, Optional
from src.data_generators import (
    TikzPoint,
    ABSTRACT_BETTER_COLOR,
    Z3_BETTER_COLOR,
    EQUAL_COLOR,
)


class ScatterPlotTikzGenerator:
    """Generates TikZ scatter plot code"""

    @staticmethod
    def generate(
        points: List[TikzPoint],
        label: str,
        title: str = "Runtime Comparison",
        xlabel: str = "Strategy A Runtime (s)",
        ylabel: str = "Strategy B Runtime (s)",
        caption: str = None,
        use_log_scale: bool = True,
    ) -> str:
        """Generate TikZ scatter plot code

        Args:
            points: Data points to plot
            title: Plot title
            xlabel: X-axis label
            ylabel: Y-axis label
            caption: Optional figure caption
            use_log_scale: If True, use log-log scale; if False, use linear scale

        Returns:
            TikZ/LaTeX code string
        """
        if not points:
            return "% No data points to plot"

        # Find data bounds
        x_vals = [p.x for p in points]
        y_vals = [p.y for p in points]

        x_min, x_max = min(x_vals), max(x_vals)
        y_min, y_max = min(y_vals), max(y_vals)

        # Use log scale bounds with safety margins
        if "Instantiation" in title:
            x_min_bound = max(10, x_min * 0.5)
            y_min_bound = max(10, y_min * 0.5)
        else:
            x_min_bound = max(0.1, x_min * 0.5)
            y_min_bound = max(0.1, y_min * 0.5)
        x_max_bound = max(x_max * 2, x_min_bound * 10)
        y_max_bound = max(y_max * 2, y_min_bound * 10)
        axis_env = "loglogaxis"

        tikz_code = f"""\\begin{{figure}}[htbp]
\\centering
\\begin{{tikzpicture}}
\\label{{{label}}}
\\begin{{{axis_env}}}[
    title={{{title}}},
    xlabel={{{xlabel}}},
    ylabel={{{ylabel}}},
    xmin={x_min_bound:.3f}, xmax={x_max_bound:.3f},
    ymin={y_min_bound:.3f}, ymax={y_max_bound:.3f},
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

        tikz_code += f"""
% Diagonal line (x=y)
\\addplot[dashed, color=black, domain={min(x_min_bound, x_max_bound):.6f}:{max(x_min_bound, x_max_bound):.6f}] {{x}};
\\end{{{axis_env}}}
\\end{{tikzpicture}}"""

        # Add caption if provided
        if caption:
            tikz_code += f"\n\\caption{{{caption}}}"

        tikz_code += "\n\\end{figure}"

        return tikz_code


class CactusPlotTikzGenerator:
    """Generates TikZ cactus plot code"""

    @staticmethod
    def generate(
        strategy_data: Dict[str, List[float]],
        title: str = "Cactus Plot",
        xlabel: str = "Number of Solved Instances",
        ylabel: str = "Runtime (s)",
        caption: str = None,
        use_log_scale: bool = True,
    ) -> str:
        """Generate a cactus plot comparing strategies

        A cactus plot shows the runtime to solve N instances, sorted by runtime.
        This gives a visual representation of how many instances each strategy
        can solve within a given time budget.

        Args:
            strategy_data: Dict mapping strategy names to sorted lists of runtimes (in seconds)
            title: Plot title
            xlabel: X-axis label (number of instances)
            ylabel: Y-axis label (runtime)
            caption: Optional figure caption
            use_log_scale: If True, use log scale for y-axis

        Returns:
            TikZ/LaTeX code string
        """
        if not strategy_data:
            return "% No strategy data to plot"

        # Find max values for axis bounds
        max_instances = max(len(runtimes) for runtimes in strategy_data.values())
        max_time = max(max(runtimes) for runtimes in strategy_data.values() if runtimes)

        # Determine axis type and bounds
        if use_log_scale:
            y_axis = "semilogyaxis"
            y_max = max_time * 1.2
        else:
            y_axis = "axis"
            y_max = max_time * 1.05
        y_min = 0.01
        x_max = max_instances * 1.05
        # Color mapping for strategies
        strategy_colors = {
            "Z3 Array Theory": Z3_BETTER_COLOR,
            "BMC Cost": ABSTRACT_BETTER_COLOR,
            "AST Size": "red",
            "Prefer Read": "pink",
            "Prefer Write": "yellow",
            "Prefer Constants": "purple",
            "Z3 MBQI": "green",
        }

        tikz_code = f"""\\begin{{figure}}[htbp]
\\centering
\\begin{{tikzpicture}}
\\label{{fig:cactus_runtime}}
\\begin{{{y_axis}}}[
    title={{{title}}},
    xlabel={{{xlabel}}},
    ylabel={{{ylabel}}},
    xmin=0, xmax={x_max:.0f},
    ymin={y_min:.3f}, ymax={y_max:.3f},
    grid=major,
    width=\\columnwidth,
    height=8cm,
    legend style={{font=\\scriptsize}},
    legend pos=south east,
]

"""

        # Plot each strategy
        for strategy_name, sorted_times in sorted(strategy_data.items()):
            tikz_code += f"\\addplot[thick, color={strategy_colors[strategy_name]}] coordinates {{\n"
            for i, runtime in enumerate(sorted_times, start=1):
                tikz_code += f"    ({i}, {runtime:.6f})\n"
            tikz_code += f"}};\n\\addlegendentry{{{strategy_name}}}\n\n"

        tikz_code += f"""\\end{{{y_axis}}}
\\end{{tikzpicture}}"""

        # Add caption if provided
        if caption:
            tikz_code += f"\n\\caption{{{caption}}}"

        tikz_code += "\n\\end{figure}"

        return tikz_code


class InstCactusPlotTikzGenerator:
    """Generates TikZ instantiation cactus plot code"""

    @staticmethod
    def generate(
        strategy_data: Dict[str, List[Optional[int]]],
        title: str = "Instantiation Cactus Plot",
        xlabel: str = "Number of Solved Instances",
        ylabel: str = "Instantiations",
        caption: str = None,
        use_log_scale: bool = True,
    ) -> str:
        """Generate an instantiation cactus plot comparing strategies

        Args:
            strategy_data: Dict mapping strategy names to sorted lists of instantiation counts.
                          None values represent failed benchmarks (pinned to top).
            title: Plot title
            xlabel: X-axis label (number of instances)
            ylabel: Y-axis label (instantiations)
            caption: Optional figure caption
            use_log_scale: If True, use log scale for y-axis

        Returns:
            TikZ/LaTeX code string
        """
        if not strategy_data:
            return "% No strategy data to plot"

        # Find max instantiation count (excluding None values) for setting bounds
        all_instantiations = []
        for inst_list in strategy_data.values():
            all_instantiations.extend([inst for inst in inst_list if inst is not None])

        if not all_instantiations:
            return "% No successful runs to plot"

        max_inst = max(all_instantiations)
        max_instances = max(len(inst_list) for inst_list in strategy_data.values())

        # Determine axis type and bounds
        if use_log_scale:
            y_axis = "semilogyaxis"
            # Pin failed runs to 2x the max successful instantiation count
            y_max = max_inst * 2
            pin_value = y_max
        else:
            y_axis = "axis"
            y_max = max_inst * 1.2
            pin_value = y_max
        y_min = 0.01
        x_max = max_instances * 1.05

        # Color mapping for strategies
        strategy_colors = {
            "Z3 Array Theory": Z3_BETTER_COLOR,
            "BMC Cost": ABSTRACT_BETTER_COLOR,
            "AST Size": "red",
            "Prefer Read": "pink",
            "Prefer Write": "yellow",
            "Prefer Constants": "purple",
            "Z3 MBQI": "green",
        }

        tikz_code = f"""\\begin{{figure}}[htbp]
\\centering
\\begin{{tikzpicture}}
\\label{{fig:cactus_inst}}
\\begin{{{y_axis}}}[
    title={{{title}}},
    xlabel={{{xlabel}}},
    ylabel={{{ylabel}}},
    xmin=0, xmax={x_max:.0f},
    ymin={y_min:.0f}, ymax={y_max:.0f},
    grid=major,
    width=\\columnwidth,
    height=8cm,
    legend style={{font=\\scriptsize}},
    legend pos=south east,
]

"""

        # Plot each strategy
        for strategy_name, inst_counts in sorted(strategy_data.items()):
            color = strategy_colors.get(strategy_name, "black")
            tikz_code += f"\\addplot[thick, color={color}] coordinates {{\n"
            for i, inst in enumerate(inst_counts, start=1):
                # Pin None (failed) values to the top of the graph
                value = pin_value if inst is None else inst
                tikz_code += f"    ({i}, {value:.0f})\n"
            tikz_code += f"}};\\addlegendentry{{{strategy_name}}}\n\n"

        tikz_code += f"""\\end{{{y_axis}}}
\\end{{tikzpicture}}"""

        # Add caption if provided
        if caption:
            tikz_code += f"\n\\caption{{{caption}}}"

        tikz_code += "\n\\end{figure}"

        return tikz_code


class TableTikzGenerator:
    """Generates LaTeX table code"""

    @staticmethod
    def generate_simple_table(
        points: List[TikzPoint], title: str = "Benchmark Results"
    ) -> str:
        """Generate LaTeX table from benchmark data points

        Args:
            points: Data points with x, y coordinates (representing two strategies)
            title: Table title

        Returns:
            LaTeX table code
        """
        if not points:
            return "% No data to table"

        table_code = f"""% Required packages: \\usepackage{{longtable}} \\usepackage{{booktabs}}
\\begin{{longtable}}{{lrrr}}
\\caption{{{title}}} \\\\
\\toprule
Example & Strategy A Runtime (s) & Strategy B Runtime (s) & Speedup \\\\
\\midrule
\\endfirsthead
\\multicolumn{{4}}{{c}}{{\\tablename\\ \\thetable\\ -- continued from previous page}} \\\\
\\toprule
Example & Strategy A Runtime (s) & Strategy B Runtime (s) & Speedup \\\\
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

    @staticmethod
    def generate_summary_statistics_table(
        grouped_results: Dict[str, Dict[str, any]],
        strategy_keys: set[str],
        baseline_strategy: str = "concrete",
    ) -> str:
        """Generate comprehensive summary statistics table comparing strategies

        Args:
            grouped_results: Dict mapping example names to strategy results
            strategy_keys: Set of all strategy keys
            baseline_strategy: Strategy to use as baseline (default: "concrete")

        Returns:
            LaTeX table code with summary statistics
        """

        # Collect statistics for each strategy
        stats = {}

        for strategy_key in strategy_keys:
            successful_benchmarks = []
            failed_benchmarks = []
            instantiations = []
            display_name = None

            for example_name, strategies in grouped_results.items():
                if strategy_key in strategies:
                    result = strategies[strategy_key]
                    # Get display name from the first result we find for this strategy
                    if display_name is None:
                        display_name = result.get_display_name()

                    if result.success:
                        successful_benchmarks.append(example_name)
                        instantiations.append(result.used_instantiations)
                    else:
                        failed_benchmarks.append(example_name)

            stats[strategy_key] = {
                "total": len(successful_benchmarks) + len(failed_benchmarks),
                "solved": len(successful_benchmarks),
                "failed": len(failed_benchmarks),
                "avg_inst": (
                    sum(instantiations) / len(instantiations) if instantiations else 0
                ),
                "successful_examples": set(successful_benchmarks),
                "display_name": display_name
                or strategy_key,  # Fallback to key if no results
            }

        # Calculate unique solves compared to baseline
        if baseline_strategy in stats:
            baseline_solved = stats[baseline_strategy]["successful_examples"]
            for strategy_key in strategy_keys:
                if strategy_key != baseline_strategy and strategy_key in stats:
                    strategy_solved = stats[strategy_key]["successful_examples"]
                    unique_solves = strategy_solved - baseline_solved
                    stats[strategy_key]["unique_solves"] = len(unique_solves)
                    stats[strategy_key]["unique_solve_examples"] = unique_solves
                else:
                    stats[strategy_key]["unique_solves"] = 0
                    stats[strategy_key]["unique_solve_examples"] = set()

        # Generate table
        table_code = """% Required packages: \\usepackage{booktabs}
\\begin{table}[htbp]
\\centering
\\caption{Summary Statistics: Strategy Performance Comparison}
\\label{tab:summary_statistics}
\\resizebox{\columnwidth}{!}{%
\\begin{tabular}{lrrrr}
\\toprule
Strategy & Solved & Failed & Unique Solves vs Z3 & Avg. Instantiations \\\\
\\midrule
"""

        # Sort strategies: baseline first, then others alphabetically
        sorted_strategies = sorted(
            strategy_keys,
            key=lambda s: (
                0 if s == baseline_strategy else 1,
                s,
            ),
        )

        for strategy_key in sorted_strategies:
            if strategy_key not in stats:
                continue

            s = stats[strategy_key]

            # Use display name from BenchmarkResult object
            display_name = s["display_name"]
            if strategy_key == baseline_strategy:
                display_name = f"{display_name} (Baseline)"

            solved = s["solved"]
            failed = s["failed"]
            unique = s.get("unique_solves", 0)
            avg_inst = s["avg_inst"]

            # Format unique solves (show as dash for baseline)
            unique_str = "---" if strategy_key == baseline_strategy else str(unique)

            # Format average instantiations
            avg_inst_str = f"{avg_inst:.0f}" if avg_inst > 0 else "---"

            table_code += f"{display_name} & {solved} & {failed} & {unique_str} & {avg_inst_str} \\\\\n"

        table_code += """\\bottomrule
\\end{tabular}%
}
\\end{table}
"""

        return table_code

    @staticmethod
    def generate_unique_solves_detail_table(
        grouped_results: Dict[str, Dict[str, any]],
        strategy_key: str,
        baseline_strategy: str = "concrete",
    ) -> str:
        """Generate detailed table of benchmarks uniquely solved by a strategy

        Args:
            grouped_results: Dict mapping example names to strategy results
            strategy_key: Strategy to analyze
            baseline_strategy: Baseline strategy for comparison

        Returns:
            LaTeX table code listing unique solves
        """
        # Find benchmarks solved by strategy but not baseline
        unique_solves = []

        for example_name, strategies in grouped_results.items():
            if strategy_key not in strategies or baseline_strategy not in strategies:
                continue

            strategy_result = strategies[strategy_key]
            baseline_result = strategies[baseline_strategy]

            if strategy_result.success and not baseline_result.success:
                unique_solves.append(
                    {
                        "example": example_name.replace("examples/", "").replace(
                            ".vmt", ""
                        ),
                        "runtime": strategy_result.runtime_ms / 1000.0,
                        "instantiations": strategy_result.used_instantiations,
                        "depth": strategy_result.depth,
                    }
                )

        if not unique_solves:
            return "% No unique solves for this strategy"

        # Sort by example name
        unique_solves.sort(key=lambda x: x["example"])

        # Create display name
        display_name = strategy_key.replace("_", " ").replace("-", " ").title()

        table_code = f"""% Required packages: \\usepackage{{longtable}} \\usepackage{{booktabs}}
\\begin{{longtable}}{{lrrr}}
\\caption{{Benchmarks Uniquely Solved by {display_name} (Not Solved by Z3)}} \\\\
\\toprule
Example & Runtime (s) & Instantiations & Depth \\\\
\\midrule
\\endfirsthead
\\multicolumn{{4}}{{c}}{{\\tablename\\ \\thetable\\ -- continued from previous page}} \\\\
\\toprule
Example & Runtime (s) & Instantiations & Depth \\\\
\\midrule
\\endhead
\\midrule
\\multicolumn{{4}}{{r}}{{Continued on next page}} \\\\
\\endfoot
\\bottomrule
\\endlastfoot
"""

        for solve in unique_solves:
            table_code += f"{solve['example']} & {solve['runtime']:.3f} & {solve['instantiations']} & {solve['depth']} \\\\\n"

        table_code += "\\end{longtable}"

        return table_code

    @staticmethod
    def generate_shared_benchmark_analysis_table(
        grouped_results: Dict[str, Dict[str, any]],
        strategy_keys: set[str],
        baseline_strategy: str = "concrete",
        min_baseline_runtime_ms: float = 1000.0,
    ) -> str:
        """Generate analysis table for shared solved benchmarks where baseline took >1s

        Compares average speedup and instantiation reduction for benchmarks that were
        successfully solved by both the baseline and each comparison strategy, where
        the baseline runtime exceeded the minimum threshold.

        Args:
            grouped_results: Dict mapping example names to strategy results
            strategy_keys: Set of all strategy keys to compare
            baseline_strategy: Strategy to use as baseline (default: "concrete")
            min_baseline_runtime_ms: Minimum baseline runtime in ms to include (default: 1000)

        Returns:
            LaTeX table code with shared benchmark analysis
        """

        # Collect statistics for each strategy comparison
        comparison_stats = {}

        for strategy_key in strategy_keys:
            if strategy_key == baseline_strategy:
                continue

            shared_benchmarks = []

            for example_name, strategies in grouped_results.items():
                if (
                    strategy_key not in strategies
                    or baseline_strategy not in strategies
                ):
                    continue

                baseline_result = strategies[baseline_strategy]
                strategy_result = strategies[strategy_key]

                # Only include if both succeeded and baseline took >1s
                if (
                    baseline_result.success
                    and strategy_result.success
                    and baseline_result.runtime_ms >= min_baseline_runtime_ms
                ):
                    speedup = (
                        baseline_result.runtime_ms / strategy_result.runtime_ms
                        if strategy_result.runtime_ms > 0
                        else float("inf")
                    )
                    inst_reduction = (
                        baseline_result.used_instantiations
                        - strategy_result.used_instantiations
                    )
                    inst_reduction_pct = (
                        (inst_reduction / baseline_result.used_instantiations * 100)
                        if baseline_result.used_instantiations > 0
                        else 0
                    )

                    shared_benchmarks.append(
                        {
                            "example": example_name,
                            "speedup": speedup,
                            "inst_reduction": inst_reduction,
                            "inst_reduction_pct": inst_reduction_pct,
                            "baseline_runtime_ms": baseline_result.runtime_ms,
                            "strategy_runtime_ms": strategy_result.runtime_ms,
                            "baseline_inst": baseline_result.used_instantiations,
                            "strategy_inst": strategy_result.used_instantiations,
                        }
                    )

            if shared_benchmarks:
                avg_speedup = sum(b["speedup"] for b in shared_benchmarks) / len(
                    shared_benchmarks
                )
                avg_inst_reduction_pct = sum(
                    b["inst_reduction_pct"] for b in shared_benchmarks
                ) / len(shared_benchmarks)

                # Get display name from first result
                display_name = None
                for example_name, strategies in grouped_results.items():
                    if strategy_key in strategies:
                        display_name = strategies[strategy_key].get_display_name()
                        break

                comparison_stats[strategy_key] = {
                    "display_name": display_name or strategy_key,
                    "shared_count": len(shared_benchmarks),
                    "avg_speedup": avg_speedup,
                    "avg_inst_reduction_pct": avg_inst_reduction_pct,
                    "benchmarks": shared_benchmarks,
                }

        if not comparison_stats:
            return "% No shared benchmarks meeting criteria"

        # Get baseline display name
        baseline_display_name = baseline_strategy
        for example_name, strategies in grouped_results.items():
            if baseline_strategy in strategies:
                baseline_display_name = strategies[baseline_strategy].get_display_name()
                break

        # Generate table
        table_code = f"""% Required packages: \\usepackage{{booktabs}}
\\begin{{table}}[htbp]
\\centering
\\caption{{Performance Analysis for Shared Solved Benchmarks ({baseline_display_name} runtime > {min_baseline_runtime_ms / 1000:.1f}s)}}
\\label{{tab:shared_benchmark_analysis}}
\\resizebox{{\\columnwidth}}{{!}}{{%
\\begin{{tabular}}{{lrrr}}
\\toprule
Strategy & Shared Benchmarks & Avg. Speedup & Avg. Inst. Reduction \\\\
\\midrule
"""

        # Sort strategies alphabetically
        sorted_strategies = sorted(comparison_stats.keys())

        for strategy_key in sorted_strategies:
            stats = comparison_stats[strategy_key]

            display_name = stats["display_name"]
            shared_count = stats["shared_count"]
            avg_speedup = stats["avg_speedup"]
            avg_inst_reduction_pct = stats["avg_inst_reduction_pct"]

            # Format speedup (handle infinity case)
            if avg_speedup == float("inf"):
                speedup_str = "$\\infty$"
            else:
                speedup_str = f"{avg_speedup:.2f}x"

            # Format instantiation reduction
            inst_str = f"{avg_inst_reduction_pct:-.1f}\\%"

            table_code += (
                f"{display_name} & {shared_count} & {speedup_str} & {inst_str} \\\\\n"
            )

        table_code += """\\bottomrule
\\end{tabular}%
}
\\end{table}
"""

        return table_code
