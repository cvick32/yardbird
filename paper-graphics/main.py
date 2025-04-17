import json
import argparse
import matplotlib.pyplot as plt
from dataclasses import dataclass
from typing import Union, override

import plotly.express as px
import plotly.graph_objects as go
import pandas as pd

# Setup global configuration variables.
BMC_DEPTH = None
BMC_TIMEOUT = None
JSON_FILE = None

# === Data Models ===

CONCRETE_ARRAY_Z3_STATS = ["array ax1", "array ax2"]
ABSTRACT_ARRAY_Z3_STATS = [
    "quant instantiations",
    "lazy quant instantiations",
    "missed quant instantiations",
]


@dataclass
class SolverStatistics:
    stats: dict[str, Union[int, float]]

    def get_concrete_array_instantiations(self):
        nums = []
        for stat in CONCRETE_ARRAY_Z3_STATS:
            try:
                nums.append(int(self.stats[stat]))
            except KeyError:
                nums.append(0)
        return sum(nums)

    def get_abstract_array_instantiations(self):
        nums = []
        for stat in ABSTRACT_ARRAY_Z3_STATS:
            try:
                nums.append(int(self.stats[stat]))
            except KeyError:
                nums.append(0)
        return sum(nums)


@dataclass
class StrategySuccess:
    used_instances: list[str]
    const_instances: list[str]
    solver_statistics: SolverStatistics
    counterexample: bool
    found_proof: bool

    def get_abstract_instantiation_count(self):
        return (
            len(self.used_instances) * BMC_DEPTH
        ) + self.solver_statistics.get_abstract_array_instantiations()

    def get_concrete_instantiation_count(self):
        return self.solver_statistics.get_concrete_array_instantiations()


@dataclass
class StrategyNoProgress:
    used_instances: list[str]
    const_instances: list[str]
    solver_statistics: SolverStatistics
    counterexample: bool
    found_proof: bool

    def get_abstract_instantiation_count(self):
        return 10000000

    def get_concrete_instantiation_count(self):
        return 10000000


@dataclass
class StrategyPanic:
    message: str

    def get_abstract_instantiation_count(self):
        return 10000000

    def get_concrete_instantiation_count(self):
        return 10000000


@dataclass
class StrategyError:
    message: str

    def get_abstract_instantiation_count(self):
        return 10000000

    def get_concrete_instantiation_count(self):
        return 10000000


@dataclass
class StrategyTimeout:
    duration_ms: int

    def get_abstract_instantiation_count(self):
        return 10000000

    def get_concrete_instantiation_count(self):
        return 10000000


StrategyOutcome = Union[
    StrategySuccess, StrategyNoProgress, StrategyPanic, StrategyTimeout, StrategyError
]


@dataclass
class StrategyResultBase:
    run_time: float
    depth: int
    outcome: StrategyOutcome

    def get_instantiations(self) -> int:
        raise ValueError("Must implement `get_instantiations()` in subclass")


@dataclass
class AbstractStrategyResult(StrategyResultBase):

    @override
    def get_instantiations(self):
        return self.outcome.get_abstract_instantiation_count()


@dataclass
class ConcreteStrategyResult(StrategyResultBase):
    @override
    def get_instantiations(self):
        return self.outcome.get_concrete_instantiation_count()


StrategyResult = Union[AbstractStrategyResult, ConcreteStrategyResult]


@dataclass
class BenchmarkResult:
    example: str
    results: list[StrategyResult]

    def get_instantiations(self) -> tuple[int, int]:
        abstract = next(
            (r for r in self.results if isinstance(r, AbstractStrategyResult)), None
        )
        concrete = next(
            (r for r in self.results if isinstance(r, ConcreteStrategyResult)), None
        )

        abstract_count = abstract.get_instantiations()
        concrete_count = concrete.get_instantiations()

        return abstract_count, concrete_count


# === Parsing Functions ===


def parse_strategy_result(entry: dict) -> StrategyResult:
    strat_type = entry["strategy"]
    raw_result = entry["result"]

    if "Success" in raw_result:
        data = raw_result["Success"]
        outcome = StrategySuccess(
            used_instances=data["used_instances"],
            const_instances=data["const_instances"],
            solver_statistics=SolverStatistics(
                stats=data["solver_statistics"]["stats"]
            ),
            counterexample=data["counterexample"],
            found_proof=data["found_proof"],
        )
    elif "NoProgress" in raw_result:
        data = raw_result["NoProgress"]
        outcome = StrategyNoProgress(
            used_instances=data["used_instances"],
            const_instances=data["const_instances"],
            solver_statistics=SolverStatistics(
                stats=data["solver_statistics"]["stats"]
            ),
            counterexample=data["counterexample"],
            found_proof=data["found_proof"],
        )
    elif "Panic" in raw_result:
        outcome = StrategyPanic(message=raw_result["Panic"])
    elif "Error" in raw_result:
        outcome = StrategyError(message=raw_result["Error"])
    elif "Timeout" in raw_result:
        outcome = StrategyTimeout(duration_ms=raw_result["Timeout"])
    else:
        raise ValueError(f"Unknown result type in entry: {raw_result}")

    common_args = {
        "run_time": entry["run_time"],
        "depth": entry["depth"],
        "outcome": outcome,
    }

    if strat_type == "abstract":
        return AbstractStrategyResult(**common_args)
    elif strat_type == "concrete":
        return ConcreteStrategyResult(**common_args)
    else:
        raise ValueError(f"Unknown strategy type: {strat_type}")


def parse_benchmark_results(json_data: str) -> list[BenchmarkResult]:
    raw = json.loads(json_data)
    benchmarks = []
    for entry in raw:
        example = entry["example"]
        results = [parse_strategy_result(r) for r in entry["result"]]
        benchmarks.append(BenchmarkResult(example=example, results=results))
    return benchmarks


def get_outcome_type(outcome: StrategyOutcome) -> str:
    if isinstance(outcome, StrategySuccess):
        return "success"
    elif isinstance(outcome, StrategyNoProgress):
        return "no_progress"
    elif isinstance(outcome, StrategyPanic):
        return "panic"
    elif isinstance(outcome, StrategyTimeout):
        return "timeout"
    elif isinstance(outcome, StrategyError):
        return "error"
    return "unknown"


# === Graph Creation Functions ===


def create_runtime_graph(benchmarks: list[BenchmarkResult], name: str):
    data = []

    for benchmark in benchmarks:
        abstract = next(
            (r for r in benchmark.results if isinstance(r, AbstractStrategyResult)),
            None,
        )
        concrete = next(
            (r for r in benchmark.results if isinstance(r, ConcreteStrategyResult)),
            None,
        )

        if abstract is None or concrete is None:
            print(benchmark)
            continue

        def get_time(result: StrategyResultBase) -> float:
            if isinstance(result.outcome, StrategySuccess):
                return result.run_time / 1000.0
            elif isinstance(result.outcome, StrategyTimeout):
                return result.outcome.duration_ms / 1000.0
            else:
                return 1800000 / 1000.0  # Default timeout in seconds

        abstract_time = round(get_time(abstract), 2)
        concrete_time = round(get_time(concrete), 2)

        data.append(
            {
                "example": benchmark.example,
                "abstract_time": abstract_time,
                "concrete_time": concrete_time,
            }
        )

    df = pd.DataFrame(data)
    # Plot using Plotly for interactivity

    df["time_performance"] = df.apply(
        lambda row: (
            "abstract faster"
            if row["abstract_time"] < row["concrete_time"]
            else "concrete faster"
        ),
        axis=1,
    )

    abstract_time_wins = (df["abstract_time"] < df["concrete_time"]).sum()
    concrete_time_wins = (df["abstract_time"] > df["concrete_time"]).sum()

    fig = px.scatter(
        df,
        y="abstract_time",
        x="concrete_time",
        hover_name="example",
        color="time_performance",
        color_discrete_sequence=px.colors.qualitative.Vivid,
        log_x=True,
        log_y=True,
        labels={
            "abstract_time": "Yardbird Runtime (s)",
            "concrete_time": "Z3 Runtime (s)",
        },
    )

    min_val = min(df["abstract_time"].min(), df["concrete_time"].min())
    max_val = max(df["abstract_time"].max(), df["concrete_time"].max())

    # Add the x = y line to the existing figure
    fig.add_trace(
        go.Scatter(
            x=[min_val, max_val],
            y=[min_val, max_val],
            mode="lines",
            line=dict(color="black", dash="dash"),
            # name="x = y",
        )
    )

    fig.update_traces(marker=dict(size=8))
    fig.update_layout(
        width=800,
        height=600,
        showlegend=False,
        plot_bgcolor="rgba(0,0,0,0)",
        paper_bgcolor="rgba(0,0,0,0)",
        xaxis=dict(showgrid=True, gridcolor="black", gridwidth=1),
        yaxis=dict(showgrid=True, gridcolor="black", gridwidth=1),
    )
    # Save as high-resolution PNG
    fig.write_image(
        f"{name}_runtime_plot.png", scale=3
    )  # scale=3 means 3x default resolution
    # fig.show()
    return (df, abstract_time_wins, concrete_time_wins)


def create_instantiation_graph(benchmarks: list[BenchmarkResult], name: str):
    data = []
    for b in benchmarks:
        abstract_inst, concrete_inst = b.get_instantiations()
        data.append(
            {
                "example": b.example,
                "abstract_instantiations": abstract_inst,
                "concrete_instantiations": concrete_inst,
            }
        )

    df = pd.DataFrame(data)
    df["inst_performance"] = df.apply(
        lambda row: (
            "abstract better"
            if row["abstract_instantiations"] <= row["concrete_instantiations"]
            else "concrete better"
        ),
        axis=1,
    )

    abstract_inst_wins = (
        df["abstract_instantiations"] < df["concrete_instantiations"]
    ).sum()
    concrete_inst_wins = (
        df["abstract_instantiations"] > df["concrete_instantiations"]
    ).sum()

    fig = px.scatter(
        df,
        y="abstract_instantiations",
        x="concrete_instantiations",
        color="inst_performance",
        color_discrete_sequence=px.colors.qualitative.Vivid,
        log_x=True,
        log_y=True,
        hover_name="example",
        labels={
            "abstract_instantiations": "# of Yardbird Quantifier Instantiations",
            "concrete_instantiations": "# of Z3 Quantifier Instantiations",
        },
    )

    min_val = min(
        df["abstract_instantiations"].min(), df["concrete_instantiations"].min()
    )
    max_val = max(
        df["abstract_instantiations"].max(), df["concrete_instantiations"].max()
    )

    # Add the x = y line to the existing figure
    fig.add_trace(
        go.Scatter(
            x=[min_val, max_val],
            y=[min_val, max_val],
            mode="lines",
            line=dict(color="black", dash="dash"),
            name="x = y",
        )
    )

    fig.update_traces(marker=dict(size=8))
    fig.update_layout(
        width=800,
        height=600,
        showlegend=False,
        plot_bgcolor="rgba(0,0,0,0)",
        paper_bgcolor="rgba(0,0,0,0)",
        xaxis=dict(showgrid=True, gridcolor="black", gridwidth=1),
        yaxis=dict(showgrid=True, gridcolor="black", gridwidth=1),
    )
    # fig.show()
    # Save as high-resolution PNG
    fig.write_image(
        f"{name}_instantiation_plot.png", scale=3
    )  # scale=3 means 3x default resolution

    return (df, abstract_inst_wins, concrete_inst_wins)


# === Helpers ===


# Function to split benchmarks based on whether abstract strategy contains "forall"
def split_by_quantification(
    benchmarks: list[BenchmarkResult],
) -> tuple[list[BenchmarkResult], list[BenchmarkResult]]:
    quantified = []
    unquantified = []
    for b in benchmarks:
        abstract = next(
            (r for r in b.results if isinstance(r, AbstractStrategyResult)), None
        )
        if isinstance(abstract, AbstractStrategyResult) and isinstance(
            abstract.outcome, (StrategySuccess, StrategyNoProgress)
        ):
            if any("forall" in inst for inst in abstract.outcome.used_instances):
                quantified.append(b)
            else:
                unquantified.append(b)
        else:
            unquantified.append(b)
    return quantified, unquantified


# === Main CLI Runner ===


def main():
    global BMC_DEPTH
    global BMC_TIMEOUT
    global JSON_FILE
    parser = argparse.ArgumentParser(description="Parse Yardbird benchmark results.")
    parser.add_argument(
        "json_file", help="Path to the JSON file with Yardbird results."
    )
    parser.add_argument("bmc_depth", help="BMC depth used to generate the JSON.")
    parser.add_argument(
        "bmc_timeout", help="Timeout used to generate the JSON in seconds."
    )

    args = parser.parse_args()

    JSON_FILE = args.json_file
    BMC_DEPTH = int(args.bmc_depth)
    BMC_TIMEOUT = int(args.bmc_timeout)

    with open(args.json_file, "r") as f:
        benchmarks = parse_benchmark_results(f.read())

    print(f"Parsed {len(benchmarks)} benchmark results.\n")
    for b in benchmarks:
        abstract_inst, concrete_inst = b.get_instantiations()
        print(f"{b.example}: abstract={abstract_inst}, concrete={concrete_inst}")

    quantified, unquantified = split_by_quantification(benchmarks)

    runtime_df, abs_time_wins, con_time_wins = create_runtime_graph(
        benchmarks, name="full"
    )
    insts_df, abs_insts_wins, con_insts_wins = create_instantiation_graph(
        benchmarks, name="full"
    )
    print(f"Abs Time Wins: {abs_time_wins}\nCon Time Wins: {con_time_wins}")
    print(f"Abs Inst Wins: {abs_insts_wins}\nCon Inst Wins: {con_insts_wins}")

    combined_df = runtime_df.merge(insts_df, on="example", how="inner")
    combined_df = combined_df.drop(columns=["time_performance", "inst_performance"])
    combined_df.sort_values(by="example", inplace=True)
    for i, row in combined_df.iterrows():
        name = row["example"]
        combined_df.at[i, "example"] = name.replace("examples/", "")
    print(
        combined_df.to_latex(
            index=False, escape=True, longtable=True, float_format="%.2f"
        )
    )
    runtime_df, abs_time_wins, con_time_wins = create_runtime_graph(
        quantified, name="quant"
    )
    insts_df, abs_insts_wins, con_insts_wins = create_instantiation_graph(
        quantified, name="quant"
    )
    runtime_df, abs_time_wins, con_time_wins = create_runtime_graph(
        unquantified, name="unquant"
    )
    insts_df, abs_insts_wins, con_insts_wins = create_instantiation_graph(
        unquantified, name="unquant"
    )

    breakpoint()


if __name__ == "__main__":
    main()
