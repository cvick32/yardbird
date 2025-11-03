from pathlib import Path
import argparse
from datetime import datetime

from src.benchmark_parsing import BenchmarkParser
from src.unique_solves import unique_solves
from src.data_generators import (
    RuntimeScatterPlotGenerator,
    CactusPlotGenerator,
    InstantiationScatterPlotGenerator,
    InstCactusPlotGenerator,
)
from src.tikz_generators import (
    ScatterPlotTikzGenerator,
    CactusPlotTikzGenerator,
    InstCactusPlotTikzGenerator,
    TableTikzGenerator,
)


def generate_figures(grouped, strategy_keys, all_results, output_dir):
    """Generate all figures and save to output directory

    Args:
        grouped: Grouped benchmark results by example
        strategy_keys: Set of all strategy keys found in results
        all_results: List of all benchmark results (for cactus plot)
        output_dir: Directory to save generated figures
    """
    output_dir.mkdir(parents=True, exist_ok=True)

    print(f"Available strategies: {sorted(strategy_keys)}")

    # Generate summary statistics table for all strategies
    print(f"\n{'=' * 60}")
    print("Generating summary statistics table")
    print(f"{'=' * 60}")

    summary_table = TableTikzGenerator.generate_summary_statistics_table(
        grouped, strategy_keys, baseline_strategy="concrete"
    )
    summary_file = output_dir / "summary_statistics.tex"
    summary_file.write_text(summary_table)
    print(f"  Saved: {summary_file}")

    # Generate shared benchmark analysis table
    print(f"\n{'=' * 60}")
    print("Generating shared benchmark analysis table")
    print(f"{'=' * 60}")

    shared_analysis_table = TableTikzGenerator.generate_shared_benchmark_analysis_table(
        grouped,
        strategy_keys,
        baseline_strategy="concrete",
        min_baseline_runtime_ms=1000.0,
    )
    shared_analysis_file = output_dir / "shared_benchmark_analysis.tex"
    shared_analysis_file.write_text(shared_analysis_table)
    print(f"  Saved: {shared_analysis_file}")

    # Separate concrete from other strategies
    non_concrete_strategies = sorted([s for s in strategy_keys if s != "concrete"])

    # Initialize generators
    runtime_gen = RuntimeScatterPlotGenerator(grouped)
    inst_gen = InstantiationScatterPlotGenerator(grouped)

    # Generate runtime and instantiation plots for each non-concrete strategy
    for strategy_key in non_concrete_strategies:
        print(f"\n{'=' * 60}")
        print(f"Generating figures for {strategy_key} vs concrete")
        print(f"{'=' * 60}")

        # Generate runtime scatter plot
        print("\n  Generating runtime scatter plot...")
        all_points = runtime_gen.generate_points(
            "concrete", strategy_key, successful_only=False
        )
        success_points = runtime_gen.generate_points(
            "concrete", strategy_key, successful_only=True
        )

        if all_points:
            # Get display name from BenchmarkResult
            display_name = None
            for example_name, strategies in grouped.items():
                if strategy_key in strategies:
                    display_name = strategies[strategy_key].get_display_name()
                    break
            display_name = display_name or strategy_key  # Fallback

            tikz_code = ScatterPlotTikzGenerator.generate(
                all_points,
                label=f"fig:{strategy_key}_runtime_scatter",
                title=f"Runtime Comparison ({display_name} vs Z3)",
                xlabel="Z3 Runtime (s)",
                ylabel=f"{display_name} Runtime (s)",
                caption=f"Runtime comparison between {display_name} and Z3.",
                use_log_scale=True,
            )

            output_file = output_dir / f"runtime_scatter_{strategy_key}.tex"
            output_file.write_text(tikz_code)
            print(f"    Saved: {output_file}")

            # Generate table for successful runs
            if success_points:
                table_code = TableTikzGenerator.generate_simple_table(
                    success_points,
                    title=f"Runtime Results: {display_name} vs Z3",
                )
                table_file = output_dir / f"runtime_table_{strategy_key}.tex"
                table_file.write_text(table_code)
                print(f"    Saved: {table_file}")

        # Generate instantiation scatter plot
        print("\n  Generating instantiation scatter plot...")
        inst_points = inst_gen.generate_points("concrete", strategy_key, bmc_depth=50)

        if inst_points:
            # Get display name from BenchmarkResult
            display_name = None
            for example_name, strategies in grouped.items():
                if strategy_key in strategies:
                    display_name = strategies[strategy_key].get_display_name()
                    break
            display_name = display_name or strategy_key  # Fallback

            tikz_code = ScatterPlotTikzGenerator.generate(
                inst_points,
                label=f"fig:{strategy_key}_inst_scatter",
                title=f"Instantiation Comparison ({display_name} vs Z3)",
                xlabel="Z3 Instantiations",
                ylabel=f"{display_name} Instantiations",
                caption=f"Array axiom instantiation comparison between {display_name} and Z3.",
                use_log_scale=True,
            )

            output_file = output_dir / f"instantiation_scatter_{strategy_key}.tex"
            output_file.write_text(tikz_code)
            print(f"    Saved: {output_file}")

        # Generate unique solves detail table
        print("\n  Generating unique solves detail table...")
        unique_solves_table = TableTikzGenerator.generate_unique_solves_detail_table(
            grouped, strategy_key, baseline_strategy="concrete"
        )
        if "No unique solves" not in unique_solves_table:
            unique_file = output_dir / f"unique_solves_{strategy_key}.tex"
            unique_file.write_text(unique_solves_table)
            print(f"    Saved: {unique_file}")
        else:
            print(f"    No unique solves for {strategy_key}")

    # Generate runtime cactus plot
    print(f"\n{'=' * 60}")
    print("Generating runtime cactus plot")
    print(f"{'=' * 60}")

    cactus_gen = CactusPlotGenerator(all_results)
    cactus_data = cactus_gen.generate_data()

    if cactus_data:
        tikz_code = CactusPlotTikzGenerator.generate(
            cactus_data,
            title="Runtime Performance Comparison",
            xlabel="Number of Solved Instances",
            ylabel="Runtime (s)",
            caption="Cactus plot comparing runtime performance across all strategies.",
            use_log_scale=True,
        )

        output_file = output_dir / "runtime_cactus_plot.tex"
        output_file.write_text(tikz_code)
        print(f"  Saved: {output_file}")

    # Generate instantiation cactus plot
    print(f"\n{'=' * 60}")
    print("Generating instantiation cactus plot")
    print(f"{'=' * 60}")

    inst_cactus_gen = InstCactusPlotGenerator(all_results)
    inst_cactus_data = inst_cactus_gen.generate_data()

    if inst_cactus_data:
        tikz_code = InstCactusPlotTikzGenerator.generate(
            inst_cactus_data,
            title="Instantiation Performance Comparison",
            xlabel="Number of Benchmarks",
            ylabel="Instantiations",
            caption="Cactus plot comparing instantiation counts across all strategies. Failed benchmarks are pinned to the top.",
            use_log_scale=True,
        )

        output_file = output_dir / "instantiation_cactus_plot.tex"
        output_file.write_text(tikz_code)
        print(f"  Saved: {output_file}")

    print(f"\n{'=' * 60}")
    print(f"All figures saved to: {output_dir}")
    print(f"{'=' * 60}")


def find_benchmark_runs_by_date(date_str, results_dir):
    """Find all benchmark runs from a specific date.

    Args:
        date_str: Date string in format YYYY-MM-DD
        results_dir: Directory to search for benchmark runs

    Returns:
        List of Path objects pointing to results.json files
    """
    try:
        # Validate date format and convert to YYYYMMDD format
        date_obj = datetime.strptime(date_str, "%Y-%m-%d")
        date_compact = date_obj.strftime("%Y%m%d")  # e.g., "20251021"
    except ValueError:
        raise ValueError(f"Invalid date format: {date_str}. Expected YYYY-MM-DD")

    results_dir = Path(results_dir)
    if not results_dir.exists():
        raise FileNotFoundError(f"Results directory not found: {results_dir}")

    # Find all directories that contain the date string (YYYYMMDD format)
    matching_dirs = []
    for item in results_dir.iterdir():
        if item.is_dir() and date_compact in item.name:
            results_file = item / "results.json"
            if results_file.exists():
                matching_dirs.append(item)

    if not matching_dirs:
        print(f"No benchmark runs found for {date_str} in {results_dir}")
        return []

    print(f"\nFound {len(matching_dirs)} benchmark run(s) for {date_str}:")
    print("=" * 60)

    json_files = []
    for dir_path in sorted(matching_dirs):
        results_file = dir_path / "results.json"
        json_files.append(results_file)
        print(f"  - {dir_path.name}/results.json")

    print("=" * 60 + "\n")

    return json_files


def main():
    parser = argparse.ArgumentParser(
        description="Analyze benchmark results and generate figures"
    )
    parser.add_argument(
        "json_files",
        nargs="*",
        type=Path,
        help="Benchmark results JSON file(s)",
    )
    parser.add_argument(
        "--day-date",
        type=str,
        help="Find all benchmark runs from a specific date (format: YYYY-MM-DD)",
    )
    parser.add_argument(
        "--results-dir",
        type=Path,
        default=Path.cwd(),
        help="Directory to search for benchmark runs when using --day-date (default: current directory)",
    )
    parser.add_argument(
        "--figures",
        action="store_true",
        help="Generate all figures (scatter plots, cactus plots, tables)",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path.cwd(),
        help="Directory to save generated figures (default: current directory)",
    )

    args = parser.parse_args()

    # Determine which JSON files to process
    if args.day_date:
        json_files = find_benchmark_runs_by_date(args.day_date, args.results_dir)
        if not json_files:
            return
    else:
        if not args.json_files:
            parser.error("Either provide json_files or use --day-date")
        json_files = args.json_files

    # Parse benchmark results
    benchmark_parser = BenchmarkParser(json_files)

    # Default: show unique solves analysis
    grouped = {}
    strategy_keys: set[str] = set()
    for result in benchmark_parser.all_results:
        if result.example_name not in grouped:
            grouped[result.example_name] = {}

        # Create strategy key
        if result.strategy == "abstract" and result.cost_function:
            strategy_key = f"{result.strategy}_{result.cost_function}"
        else:
            strategy_key = result.strategy
        strategy_keys.add(strategy_key)
        grouped[result.example_name][strategy_key] = result

    if args.figures:
        # Generate all figures
        generate_figures(
            grouped, strategy_keys, benchmark_parser.all_results, args.output_dir
        )
    else:
        unique_solves(grouped, strategy_keys)


if __name__ == "__main__":
    main()
