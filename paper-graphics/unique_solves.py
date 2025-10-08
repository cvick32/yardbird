#!/usr/bin/env python3

import json
import sys
from pathlib import Path
from dataclasses import dataclass
from typing import List, Dict, Optional


@dataclass
class BenchmarkResult:
    """Represents a single benchmark result with strategy outcomes"""

    example_name: str
    strategy: str
    cost_function: Optional[str]
    runtime_ms: float
    depth: int
    result_type: str
    success: bool


class BenchmarkParser:
    """Parser for benchmark JSON results"""

    def __init__(self, json_paths: List[Path]):
        self.all_results = []

        for json_path in json_paths:
            with open(json_path) as f:
                data = json.load(f)

            # Parse all benchmarks from this file
            for benchmark in data.get("benchmarks", []):
                example_full = benchmark["example"]
                example_name = self._extract_clean_example_name(example_full)

                for result_entry in benchmark.get("result", []):
                    result = self._parse_single_result(example_name, result_entry)
                    if result:
                        self.all_results.append(result)

    def _extract_clean_example_name(self, full_name: str) -> str:
        """Extract clean example name from full config-prefixed name"""
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
        result_type = list(result_data.keys())[0] if result_data else "Unknown"

        success = False
        if result_type == "Success":
            success = True

        return BenchmarkResult(
            example_name=example_name,
            strategy=strategy,
            cost_function=cost_function,
            runtime_ms=runtime_ms,
            depth=depth,
            result_type=result_type,
            success=success,
        )


def main():
    if len(sys.argv) < 2:
        print("Usage: unique_solves.py <json_file1> [json_file2 ...]")
        sys.exit(1)

    json_files = [Path(f) for f in sys.argv[1:]]
    parser = BenchmarkParser(json_files)

    # Group results by example
    grouped = {}
    for result in parser.all_results:
        if result.example_name not in grouped:
            grouped[result.example_name] = {}

        # Create strategy key
        if result.strategy == "abstract" and result.cost_function:
            strategy_key = f"{result.strategy}_{result.cost_function}"
        else:
            strategy_key = result.strategy

        grouped[result.example_name][strategy_key] = result

    # Find unique solves for each strategy
    concrete_only = []
    symbol_cost_only = []
    ast_size_only = []

    for example_name, strategies in grouped.items():
        concrete = strategies.get("concrete")
        symbol_cost = strategies.get("abstract_symbol-cost")
        ast_size = strategies.get("abstract_a-s-t-size")

        # Check if concrete is the only one that succeeded
        if concrete and concrete.success:
            other_success = (
                (symbol_cost and symbol_cost.success) or (ast_size and ast_size.success)
            )
            if not other_success:
                concrete_only.append(example_name)

        # Check if symbol-cost is the only one that succeeded
        if symbol_cost and symbol_cost.success:
            other_success = (
                (concrete and concrete.success) or (ast_size and ast_size.success)
            )
            if not other_success:
                symbol_cost_only.append(example_name)

        # Check if ast-size is the only one that succeeded
        if ast_size and ast_size.success:
            other_success = (
                (concrete and concrete.success) or (symbol_cost and symbol_cost.success)
            )
            if not other_success:
                ast_size_only.append(example_name)

    # Print results
    print("\n=== UNIQUE SOLVES ===\n")

    print(f"Z3 Concrete Only ({len(concrete_only)}):")
    for example in sorted(concrete_only):
        clean_name = example.replace("examples/", "").replace(".vmt", "")
        print(f"  - {clean_name}")

    print(f"\nAbstract (symbol-cost) Only ({len(symbol_cost_only)}):")
    for example in sorted(symbol_cost_only):
        clean_name = example.replace("examples/", "").replace(".vmt", "")
        print(f"  - {clean_name}")

    print(f"\nAbstract (AST size) Only ({len(ast_size_only)}):")
    for example in sorted(ast_size_only):
        clean_name = example.replace("examples/", "").replace(".vmt", "")
        print(f"  - {clean_name}")


if __name__ == "__main__":
    main()
