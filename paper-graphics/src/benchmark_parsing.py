from dataclasses import dataclass, field
import json
from pathlib import Path
import re
from typing import Optional

CONCRETE_ARRAY_Z3_STATS = ["array ax1", "array ax2"]
ABSTRACT_WITH_QUANTIFIERS = ["quant instantiations"]
SOLVED_RESULT_TYPES = {"Success", "_FoundProof"}
JSON_READ_CHUNK_SIZE = 1024 * 1024


def _slug(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", "-", value.lower()).strip("-")


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
    num_checks: int
    egraph_builder: Optional[str] = None
    solver: Optional[str] = None
    instantiation_ranker: Optional[str] = None
    candidate_winners_per_group: Optional[int] = None
    property_check_mode: Optional[str] = None
    instantiation_strategy: Optional[str] = None
    preprocess_exact_read_after_write: Optional[bool] = None
    solver_time_s: float = 0.0  # Time spent in Z3 solver (seconds)
    total_conflicts: Optional[float] = None
    solver_stats: dict[str, float] = field(default_factory=dict)

    def has_extended_configuration(self) -> bool:
        return any(
            value is not None
            for value in (
                self.instantiation_ranker,
                self.candidate_winners_per_group,
                self.property_check_mode,
                self.instantiation_strategy,
                self.preprocess_exact_read_after_write,
            )
        )

    def get_configuration(self) -> dict[str, object]:
        return {
            "solver": self.solver,
            "strategy": self.strategy,
            "cost_function": self.cost_function,
            "depth": self.depth,
            "egraph_builder": self.egraph_builder,
            "instantiation_ranker": self.instantiation_ranker,
            "candidate_winners_per_group": self.candidate_winners_per_group,
            "property_check_mode": self.property_check_mode,
            "instantiation_strategy": self.instantiation_strategy,
            "preprocess_exact_read_after_write": (
                self.preprocess_exact_read_after_write
            ),
        }

    def get_strategy_id(self) -> str:
        if self.strategy == "abstract" and self.cost_function:
            strategy_id = f"{self.strategy}_{self.cost_function}"
            if self.has_extended_configuration():
                components: list[tuple[str, object | None]] = [
                    ("solver", self.solver),
                    ("depth", self.depth),
                    ("egraph", self.egraph_builder),
                    ("ranker", self.instantiation_ranker),
                    ("winners", self.candidate_winners_per_group),
                    ("property", self.property_check_mode),
                    ("instantiation", self.instantiation_strategy),
                    (
                        "preprocess",
                        ("on" if self.preprocess_exact_read_after_write else "off"),
                    ),
                ]
                suffix = "__".join(
                    f"{name}-{_slug(str(value))}"
                    for name, value in components
                    if value is not None
                )
                return f"{strategy_id}__{suffix}"
            if self.egraph_builder and self.egraph_builder != "full":
                strategy_id = f"{strategy_id}_{self.egraph_builder}"
            return strategy_id
        return self.strategy

    def get_display_name(self) -> str:
        if self.strategy == "concrete":
            return "Z3 Array Theory"
        elif self.strategy == "abstract-with-quantifiers":
            return "Z3 MBQI"
        elif self.strategy == "abstract":
            display_names = {
                "bmc-cost": "BMC Cost",
                "symbol-cost": "BMC Cost",
                "a-s-t-size": "AST Size",
                "ast-size": "AST Size",
                "adaptive-cost": "Adaptive Cost",
                "split-cost": "Split Cost",
                "prefer-read": "Prefer Read",
                "prefer-write": "Prefer Write",
                "prefer-constants": "Prefer Constants",
                "logistic-regression": "Logistic Regression",
                "index-aware-cost": "Index-Aware Cost",
            }
            name = display_names.get(
                self.cost_function,
                self.cost_function.replace("-", " ").title()
                if self.cost_function
                else "Abstract",
            )
            if self.has_extended_configuration():
                if self.depth:
                    name = f"{name} d{self.depth}"
                details = []
                if self.solver and self.solver != "z3":
                    details.append(self.solver.upper())
                egraph_names = {
                    "full": "full",
                    "source-then-full": "source/full",
                    "cone-then-full": "cone/full",
                }
                if self.egraph_builder:
                    details.append(
                        egraph_names.get(
                            self.egraph_builder,
                            self.egraph_builder.replace("-", " "),
                        )
                    )
                ranker_names = {
                    "prefer-source": "source rank",
                    "term-cost": "term rank",
                }
                if self.instantiation_ranker:
                    details.append(
                        ranker_names.get(
                            self.instantiation_ranker,
                            self.instantiation_ranker.replace("-", " "),
                        )
                    )
                if self.candidate_winners_per_group is not None:
                    details.append(f"N={self.candidate_winners_per_group}")
                property_names = {
                    "scoped": "scoped",
                    "assumptions": "assuming",
                }
                if self.property_check_mode:
                    details.append(
                        property_names.get(
                            self.property_check_mode,
                            self.property_check_mode.replace("-", " "),
                        )
                    )
                if (
                    self.instantiation_strategy
                    and self.instantiation_strategy != "full-unroll"
                ):
                    details.append(self.instantiation_strategy.replace("-", " "))
                if self.preprocess_exact_read_after_write:
                    details.append("exact R/W")
                if details:
                    name = f"{name} [{', '.join(details)}]"
                return name
            if self.egraph_builder and self.egraph_builder != "full":
                name = f"{name} + {self.egraph_builder.replace('-', ' ').title()}"
            return name
        else:
            return self.strategy.replace("-", " ").title()

    def get_plot_style(self) -> Optional[str]:
        """Return a semantic PGFPlots style for an ablation configuration."""
        if self.strategy != "abstract" or not self.has_extended_configuration():
            return None
        if self.instantiation_ranker == "term-cost":
            return "color=black, very thick, solid, mark=none"

        winner_colors = {
            1: "softBlue",
            4: "softGreen",
            16: "softOrange",
            48: "softPurple",
        }
        color = winner_colors.get(self.candidate_winners_per_group, "softTeal")
        line = (
            "densely dashed"
            if self.egraph_builder in {"source-then-full", "cone-then-full"}
            else "solid"
        )
        marker = (
            "mark=*, mark repeat=12, mark size=1.1pt"
            if self.property_check_mode == "assumptions"
            else "mark=none"
        )
        return f"color={color}, {line}, {marker}"


def iter_benchmark_entries(json_path: Path):
    """Yield Garden benchmark entries without retaining the complete JSON file."""
    decoder = json.JSONDecoder()
    marker = re.compile(r'"benchmarks"\s*:\s*\[')

    with json_path.open(encoding="utf-8") as input_file:
        buffer = ""
        while True:
            match = marker.search(buffer)
            if match is not None:
                buffer = buffer[match.end() :]
                break
            chunk = input_file.read(JSON_READ_CHUNK_SIZE)
            if not chunk:
                raise ValueError(f"No benchmarks array found in {json_path}")
            buffer += chunk
            if len(buffer) > JSON_READ_CHUNK_SIZE * 2:
                buffer = buffer[-JSON_READ_CHUNK_SIZE * 2 :]

        reached_eof = False
        while True:
            buffer = buffer.lstrip()
            if buffer.startswith("]"):
                return
            if buffer.startswith(","):
                buffer = buffer[1:].lstrip()

            try:
                entry, end = decoder.raw_decode(buffer)
            except json.JSONDecodeError as error:
                if reached_eof:
                    raise ValueError(
                        f"Invalid or truncated benchmarks array in {json_path}"
                    ) from error
                chunk = input_file.read(JSON_READ_CHUNK_SIZE)
                if chunk:
                    buffer += chunk
                else:
                    reached_eof = True
                continue

            if not isinstance(entry, dict):
                raise ValueError(f"Invalid benchmark entry in {json_path}")
            yield entry
            buffer = buffer[end:]


def group_benchmark_results(
    results: list[BenchmarkResult],
) -> tuple[dict[str, dict[str, BenchmarkResult]], set[str]]:
    """Group results while rejecting configuration-identity collisions."""
    grouped: dict[str, dict[str, BenchmarkResult]] = {}
    strategy_keys: set[str] = set()
    for result in results:
        strategy_id = result.get_strategy_id()
        strategies = grouped.setdefault(result.example_name, {})
        if strategy_id in strategies:
            raise ValueError(
                "Duplicate benchmark/configuration pair: "
                f"{result.example_name} / {strategy_id}"
            )
        strategies[strategy_id] = result
        strategy_keys.add(strategy_id)
    return grouped, strategy_keys


def successful_payload(full_entry: dict, success: bool) -> dict:
    if not success:
        return {}
    result = full_entry.get("result", {})
    for result_type in SOLVED_RESULT_TYPES:
        payload = result.get(result_type)
        if isinstance(payload, dict):
            return payload
    return {}


def compute_axiom_instantiations(full_entry: dict, strategy: str, success: bool) -> int:
    """Compute axiom instantiations for a benchmark result"""
    if not success:
        return 10000000  # Large penalty for unsuccessful results
    entry = successful_payload(full_entry, success)
    if strategy == "abstract":
        return int(entry.get("total_instantiations_added") or 0)
    elif strategy == "concrete":
        # Concrete: sum of concrete Z3 array axiom stats
        concrete_z3_count = 0
        for stat in CONCRETE_ARRAY_Z3_STATS:
            try:
                concrete_z3_count += int(
                    entry["solver_statistics"]["stats"].get(stat, 0)
                )
            except (ValueError, TypeError):
                pass
        return concrete_z3_count
    elif strategy == "abstract-with-quantifiers":
        quant_count = 0
        for stat in ABSTRACT_WITH_QUANTIFIERS:
            try:
                quant_count += int(entry["solver_statistics"]["stats"].get(stat, 0))
            except (ValueError, TypeError):
                pass
        return quant_count

    raise ValueError(f"Unknown strategy: {strategy}")


def find_num_checks(full_entry: dict, strategy: str, success: bool) -> int:
    """Compute axiom instantiations for a benchmark result"""
    if not success:
        return 10000000  # Large penalty for unsuccessful results
    entry = successful_payload(full_entry, success)
    try:
        stats = entry["solver_statistics"]["stats"]
        return int(stats.get("total.num checks", stats.get("num checks")) or 0)
    except (KeyError, ValueError, TypeError):
        return 0


def extract_solver_time(full_entry: dict, success: bool) -> float:
    """Extract solver time from benchmark result (in seconds)"""
    if not success:
        return 0.0
    try:
        entry = successful_payload(full_entry, success)
        stats = entry["solver_statistics"]["stats"]
        solver_time = stats.get("total_solver_time", stats.get("solver_time", 0.0))
        return float(solver_time)
    except (KeyError, ValueError, TypeError):
        return 0.0


def extract_total_conflicts(full_entry: dict, success: bool) -> Optional[float]:
    """Extract the solver's cumulative conflict count for a solved benchmark."""
    if not success:
        return None
    try:
        entry = successful_payload(full_entry, success)
        stats = entry["solver_statistics"]["stats"]
        conflicts = stats.get("total.conflicts", stats.get("conflicts"))
        return float(conflicts) if conflicts is not None else None
    except (KeyError, ValueError, TypeError):
        return None


def extract_solver_stats(full_entry: dict, success: bool) -> dict[str, float]:
    """Extract all numeric Z3 statistics for later paired diagnostics."""
    if not success:
        return {}

    try:
        stats = successful_payload(full_entry, success)["solver_statistics"]["stats"]
    except (KeyError, TypeError):
        return {}

    numeric_stats: dict[str, float] = {}
    for key, value in stats.items():
        if isinstance(value, bool):
            continue
        try:
            numeric_stats[str(key)] = float(value)
        except (ValueError, TypeError):
            continue
    for key, value in list(numeric_stats.items()):
        if key.startswith("total."):
            numeric_stats[key.removeprefix("total.")] = value
    return numeric_stats


class BenchmarkParser:
    """Parser for benchmark JSON results"""

    def __init__(self, json_paths: list[Path]):
        self.all_results = []

        for json_path in json_paths:
            for benchmark in iter_benchmark_entries(json_path):
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
        egraph_builder = result_entry.get("egraph_builder")
        solver = result_entry.get("solver")
        instantiation_ranker = result_entry.get("instantiation_ranker")
        candidate_winners_per_group = result_entry.get("candidate_winners_per_group")
        property_check_mode = result_entry.get("property_check_mode")
        instantiation_strategy = result_entry.get("instantiation_strategy")
        preprocess_exact_read_after_write = (
            result_entry.get("preprocess_exact_read_after_write")
            if "preprocess_exact_read_after_write" in result_entry
            else None
        )
        runtime_ms = result_entry.get("run_time", 0)
        depth = result_entry.get("depth", 0)

        result_data = result_entry.get("result", {})
        result_type = list(result_data.keys())[0] if result_data else "Unknown"

        success = result_type in SOLVED_RESULT_TYPES

        used_instantiations = compute_axiom_instantiations(
            result_entry, strategy, success
        )
        solver_time = extract_solver_time(result_entry, success)
        total_conflicts = extract_total_conflicts(result_entry, success)
        solver_stats = extract_solver_stats(result_entry, success)

        return BenchmarkResult(
            example_name=example_name,
            strategy=strategy,
            cost_function=cost_function,
            egraph_builder=egraph_builder,
            solver=solver,
            instantiation_ranker=instantiation_ranker,
            candidate_winners_per_group=candidate_winners_per_group,
            property_check_mode=property_check_mode,
            instantiation_strategy=instantiation_strategy,
            preprocess_exact_read_after_write=preprocess_exact_read_after_write,
            runtime_ms=runtime_ms,
            depth=depth,
            result_type=result_type,
            success=success,
            used_instantiations=used_instantiations,
            num_checks=find_num_checks(result_entry, strategy, success),
            solver_time_s=solver_time,
            total_conflicts=total_conflicts,
            solver_stats=solver_stats,
        )
