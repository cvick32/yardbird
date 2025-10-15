"""TikZ/LaTeX code generators for benchmark visualization"""

from typing import List, Dict
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

        if use_log_scale:
            # Use log scale bounds with safety margins
            x_min_bound = max(0.001, x_min * 0.5)
            y_min_bound = max(0.001, y_min * 0.5)
            x_max_bound = max(x_max * 2, x_min_bound * 10)
            y_max_bound = max(y_max * 2, y_min_bound * 10)
            axis_env = "loglogaxis"
        else:
            # Use linear scale bounds with padding
            x_range = x_max - x_min
            y_range = y_max - y_min
            x_min_bound = max(0, x_min - 0.05 * x_range)
            y_min_bound = max(0, y_min - 0.05 * y_range)
            x_max_bound = x_max + 0.05 * x_range
            y_max_bound = y_max + 0.05 * y_range
            axis_env = "axis"

        tikz_code = f"""\\begin{{figure}}[htbp]
\\centering
\\begin{{tikzpicture}}
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
            y_min = 0.001  # Small positive value for log scale
            y_max = max_time * 1.2
        else:
            y_axis = "axis"
            y_min = 0
            y_max = max_time * 1.05

        x_max = max_instances * 1.05

        # Color mapping for strategies
        strategy_colors = {
            "concrete": ("Z3", Z3_BETTER_COLOR),
            "Z3": ("Z3", Z3_BETTER_COLOR),
            "abstract_symbol-cost": ("BMC Cost", ABSTRACT_BETTER_COLOR),
            "abstract_a-s-t-size": ("AST Size", "red"),
            "Abstract (symbol-cost)": ("BMC Cost", ABSTRACT_BETTER_COLOR),
            "Abstract (AST size)": ("AST Size", "red"),
            "Abstract (a-s-t-size)": ("AST Size", "red"),
        }

        tikz_code = f"""\\begin{{figure}}[htbp]
\\centering
\\begin{{tikzpicture}}
\\begin{{{y_axis}}}[
    title={{{title}}},
    xlabel={{{xlabel}}},
    ylabel={{{ylabel}}},
    xmin=0, xmax={x_max:.0f},
    ymin={y_min:.3f}, ymax={y_max:.3f},
    grid=major,
    width=\\columnwidth,
    height=8cm,
    legend pos=north west
]

"""

        # Plot each strategy
        for strategy_name, sorted_times in sorted(strategy_data.items()):
            color_info = strategy_colors.get(strategy_name, (strategy_name, "blue"))
            legend_name, color = color_info

            tikz_code += f"\\addplot[thick, color={color}] coordinates {{\n"
            for i, runtime in enumerate(sorted_times, start=1):
                tikz_code += f"    ({i}, {runtime:.6f})\n"
            tikz_code += f"}};\n\\addlegendentry{{{legend_name}}}\n\n"

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
