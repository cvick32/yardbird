from dataclasses import dataclass
import json
from pathlib import Path
from typing import Optional

CONCRETE_ARRAY_Z3_STATS = ["array ax1", "array ax2"]
ABSTRACT_WITH_QUANTIFIERS = ["quant instantiations"]


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
    used_instantiations: int


def compute_axiom_instantiations(full_entry: dict, strategy: str, success: bool) -> int:
    """Compute axiom instantiations for a benchmark result"""
    if not success:
        return 10000000  # Large penalty for unsuccessful results
    entry = full_entry["result"]["Success"]
    if strategy == "abstract":
        return entry.get("total_instantiations_added")
    elif strategy == "concrete":
        # Concrete: sum of concrete Z3 array axiom stats
        concrete_z3_count = 0
        for stat in CONCRETE_ARRAY_Z3_STATS:
            try:
                concrete_z3_count += int(entry["solver_statistics"].get(stat, 0))
            except (ValueError, TypeError):
                pass

        return concrete_z3_count
    elif strategy == "abstract-with-quantifiers":
        quant_count = 0
        for stat in ABSTRACT_WITH_QUANTIFIERS:
            try:
                quant_count += int(entry["solver_statistics"].get(stat, 0))
            except (ValueError, TypeError):
                pass
        return quant_count

    raise ValueError(f"Unknown strategy: {strategy}")


class BenchmarkParser:
    """Parser for benchmark JSON results"""

    def __init__(self, json_paths: list[Path]):
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
        self, example_name: str, result_entry: dict
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

        used_instantiations = compute_axiom_instantiations(
            result_entry, strategy, success
        )
        return BenchmarkResult(
            example_name=example_name,
            strategy=strategy,
            cost_function=cost_function,
            runtime_ms=runtime_ms,
            depth=depth,
            result_type=result_type,
            success=success,
            used_instantiations=used_instantiations,
        )
