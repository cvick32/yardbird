"""Figure generator classes for benchmark visualization"""

from dataclasses import dataclass
from typing import List, Dict, Optional

# Import from parent package
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from src.benchmark_parsing import BenchmarkResult


# Constants for plotting
ABSTRACT_BETTER_COLOR = "orange"
Z3_BETTER_COLOR = "cyan!50!blue"
EQUAL_COLOR = "black"
TIMEOUT_MS = 1200000


@dataclass
class TikzPoint:
    """Point for TikZ plotting"""

    x: float
    y: float
    label: str
    color: str = Z3_BETTER_COLOR


class RuntimeScatterPlotGenerator:
    """Generates runtime comparison scatter plots between two strategies"""

    def __init__(self, grouped_results: Dict[str, Dict[str, BenchmarkResult]]):
        """Initialize generator with grouped results

        Args:
            grouped_results: Dict from group_results_by_example()
        """
        self.grouped_results = grouped_results

    def generate_points(
        self,
        strategy_a_key: str,
        strategy_b_key: str,
        successful_only: bool = False,
    ) -> List[TikzPoint]:
        points = []
        for example_name, strategies in self.grouped_results.items():
            if strategy_a_key not in strategies or strategy_b_key not in strategies:
                raise ValueError(
                    f"Unknown strategies: {strategy_a_key} or {strategy_b_key} not in {strategies}"
                )

            result1 = strategies[strategy_a_key]
            result2 = strategies[strategy_b_key]

            # Skip if successful_only is True and either strategy failed
            if successful_only and (not result1.success or not result2.success):
                continue

            time1 = result1.runtime_ms if result1.success else TIMEOUT_MS
            time2 = result2.runtime_ms if result2.success else TIMEOUT_MS

            # Determine color based on which is faster
            if time2 < time1:
                color = ABSTRACT_BETTER_COLOR
            elif time2 > time1:
                color = Z3_BETTER_COLOR
            else:
                color = EQUAL_COLOR

            # Clean up label
            label = example_name.replace("examples/", "").replace(".vmt", "")

            # Convert milliseconds to seconds for plotting
            time1_s = time1 / 1000.0
            time2_s = time2 / 1000.0

            points.append(TikzPoint(x=time1_s, y=time2_s, label=label, color=color))

        return points

    def get_comparison_data(
        self,
        strategy_a_key: str,
        strategy_b_key: str,
        cost_function: Optional[str] = None,
    ) -> List[tuple]:
        """Get all benchmark comparison data including unsuccessful results

        Args:
            strategy1: First strategy name
            strategy2: Second strategy name
            cost_function: Cost function for abstract strategy

        Returns:
            List of (label, result1, result2) tuples
        """
        comparison_data = []
        for example_name, strategies in self.grouped_results.items():
            if strategy_a_key not in strategies or strategy_b_key not in strategies:
                continue

            result1 = strategies[strategy_a_key]
            result2 = strategies[strategy_b_key]

            # Clean up label
            label = example_name.replace("examples/", "").replace(".vmt", "")

            comparison_data.append((label, result1, result2))

        return comparison_data


class CactusPlotGenerator:
    """Generates cactus plots for strategy comparison"""

    def __init__(self, all_results: List[BenchmarkResult]):
        """Initialize generator with all results

        Args:
            all_results: List of all benchmark results
        """
        self.all_results = all_results

    def generate_data(
        self,
    ) -> Dict[str, List[float]]:
        """Get runtime data for cactus plot

        Args:
            strategies: List of strategy names to include
            cost_functions: Optional list of cost functions for abstract strategies

        Returns:
            Dict mapping display names to sorted runtimes in seconds
        """
        strategy_runtimes = {}
        for result in self.all_results:
            # Add runtime in seconds (convert from ms)
            runtime_ms = result.runtime_ms if result.success else TIMEOUT_MS
            runtime_s = runtime_ms / 1000.0
            if result.get_display_name() in strategy_runtimes:
                strategy_runtimes[result.get_display_name()].append(runtime_s)
            else:
                strategy_runtimes[result.get_display_name()] = [runtime_s]

        # Sort each strategy's runtimes for cactus plot
        for display_name in strategy_runtimes:
            strategy_runtimes[display_name].sort()

        return strategy_runtimes


class InstantiationScatterPlotGenerator:
    """Generates axiom instantiation comparison scatter plots"""

    # Constants for axiom instantiation counting
    CONCRETE_ARRAY_Z3_STATS = ["array ax1", "array ax2"]

    def __init__(self, grouped_results: Dict[str, Dict[str, BenchmarkResult]]):
        """Initialize generator with grouped results

        Args:
            grouped_results: Dict from group_results_by_example()
        """
        self.grouped_results = grouped_results

    def generate_points(
        self,
        strategy1_key: str,
        strategy2_key: str,
        bmc_depth: int = 50,
    ) -> List[TikzPoint]:
        """Generate scatter plot points for instantiation comparison

        Args:
            strategy1_key: First strategy key
            strategy2_key: Second strategy key
            bmc_depth: BMC depth for calculations

        Returns:
            List of TikzPoint objects for plotting (only successful runs)
        """
        points = []

        for example_name, strategies in self.grouped_results.items():
            if strategy1_key not in strategies or strategy2_key not in strategies:
                continue

            result1 = strategies[strategy1_key]
            result2 = strategies[strategy2_key]

            # Skip if either strategy failed (only plot successful runs)
            if not result1.success or not result2.success:
                continue

            inst1 = result1.used_instantiations
            inst2 = result2.used_instantiations

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


class InstCactusPlotGenerator:
    """Generates instantiation cactus plots for strategy comparison"""

    def __init__(self, all_results: List[BenchmarkResult]):
        """Initialize generator with all results

        Args:
            all_results: List of all benchmark results
        """
        self.all_results = all_results

    def generate_data(self) -> Dict[str, List[Optional[int]]]:
        """Get instantiation data for cactus plot

        Returns:
            Dict mapping display names to sorted instantiation counts.
            Failed benchmarks are represented as None (will be pinned to top of plot).
        """
        strategy_instantiations = {}

        for result in self.all_results:
            display_name = result.get_display_name()

            # Use actual instantiation count for successful runs, None for failures
            inst_count = result.used_instantiations if result.success else None
            if display_name in strategy_instantiations:
                strategy_instantiations[display_name].append(inst_count)
            else:
                strategy_instantiations[display_name] = [inst_count]

        # Sort each strategy's instantiation counts for cactus plot
        # None values (failures) will sort to the end
        for display_name in strategy_instantiations:
            strategy_instantiations[display_name].sort(
                key=lambda x: (x is None, x if x is not None else 0)
            )

        return strategy_instantiations
