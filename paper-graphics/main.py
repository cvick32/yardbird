from pathlib import Path
import sys

from src.benchmark_parsing import BenchmarkParser
from src.unique_solves import unique_solves


def main():
    if len(sys.argv) < 2:
        print("Usage: main.py [json_file1, json_file2, ...]")
        sys.exit(1)

    json_files = [Path(f) for f in sys.argv[1:]]
    parser = BenchmarkParser(json_files)

    # Group results by example
    grouped = {}
    strategy_keys: set[str] = set()
    for result in parser.all_results:
        if result.example_name not in grouped:
            grouped[result.example_name] = {}

        # Create strategy key
        if result.strategy == "abstract" and result.cost_function:
            strategy_key = f"{result.strategy}_{result.cost_function}"
        else:
            strategy_key = result.strategy
        strategy_keys.add(strategy_key)
        grouped[result.example_name][strategy_key] = result

    unique_solves(grouped, strategy_keys)


if __name__ == "__main__":
    main()
