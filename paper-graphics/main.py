from pathlib import Path
import argparse

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
            # Create readable name for strategy
            display_name = strategy_key.replace("_", " ").replace("-", " ").title()

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
            display_name = strategy_key.replace("_", " ").replace("-", " ").title()

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
            caption="Cactus plot comparing runtime performance across all benchmarks.",
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
            caption="Cactus plot comparing instantiation counts across all benchmarks. Failed benchmarks are pinned to the top.",
            use_log_scale=True,
        )

        output_file = output_dir / "instantiation_cactus_plot.tex"
        output_file.write_text(tikz_code)
        print(f"  Saved: {output_file}")

    print(f"\n{'=' * 60}")
    print(f"All figures saved to: {output_dir}")
    print(f"{'=' * 60}")


def main():
    parser = argparse.ArgumentParser(
        description="Analyze benchmark results and generate figures"
    )
    parser.add_argument(
        "json_files",
        nargs="+",
        type=Path,
        help="Benchmark results JSON file(s)",
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

    # Parse benchmark results
    benchmark_parser = BenchmarkParser(args.json_files)

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
