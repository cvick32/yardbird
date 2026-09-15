"""The experiment policy and the agent's deliberately narrow action protocol."""

from typing import Annotated, Literal

from pydantic import BaseModel, ConfigDict, Field, TypeAdapter, field_validator, model_validator


class StrictModel(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    @field_validator("candidate_winners_per_group", mode="before", check_fields=False)
    @classmethod
    def integer_winners(cls, value):
        if value is not None and type(value) is not int:
            raise ValueError("candidate_winners_per_group must be an integer")
        return value


Cost = Literal[
    "bmc-cost",
    "protocol-bmc",
    "ast-size",
    "adaptive-cost",
    "split-cost",
    "prefer-read",
    "prefer-write",
    "prefer-constants",
    "index-aware",
    "generated",
    "logistic-regression",
]
Builder = Literal["full", "source-then-full", "cone-then-full"]
Winners = Literal[1, 2, 5, 10, 20, 50]
Ranker = Literal["term-cost", "prefer-source"]
PropertyMode = Literal["scoped", "assumptions", "refinement-assumptions"]
View = Literal[
    "overview",
    "depth",
    "refinement",
    "timing",
    "rules",
    "quantifiers",
    "egraph",
    "solver",
    "events",
]


class ExperimentConfig(StrictModel):
    strategy: Literal["abstract", "concrete"] = "abstract"
    cost_function: Cost = "protocol-bmc"
    egraph_builder: Builder = "source-then-full"
    candidate_winners_per_group: Winners = 20
    instantiation_ranker: Ranker = "prefer-source"
    property_check_mode: PropertyMode = "assumptions"


class ConfigPatch(StrictModel):
    cost_function: Cost | None = None
    egraph_builder: Builder | None = None
    candidate_winners_per_group: Winners | None = None
    instantiation_ranker: Ranker | None = None
    property_check_mode: PropertyMode | None = None


def resolve_patch(
    parent: ExperimentConfig, patch: ConfigPatch, has_ranker: bool
) -> ExperimentConfig:
    if parent.strategy != "abstract":
        raise ValueError(
            "Adaptive runs must descend from an abstract run, not the concrete reference"
        )
    updates = patch.model_dump(exclude_none=True)
    changed = sum(getattr(parent, key) != value for key, value in updates.items())
    if changed > 3:
        raise ValueError("At most three tuning dimensions may change relative to the parent")
    result = ExperimentConfig.model_validate(parent.model_dump() | updates)
    if result.cost_function == "logistic-regression" and not has_ranker:
        raise ValueError("logistic-regression requires a pinned ranker model")
    return result


class SchedulerConfig(StrictModel):
    max_parallel_runs: int = Field(default=2, ge=1, le=128)
    max_parallel_agents: int = Field(default=2, ge=1, le=128)
    # Descriptive resource reservations in v1; affinity/cgroups are not enforced.
    cpus_per_run: int | None = Field(default=None, ge=1)
    memory_per_run_gb: float | None = Field(default=None, gt=0)


class CampaignConfig(StrictModel):
    benchmarks: list[str] = Field(min_length=1)
    depth: int = Field(default=20, ge=1, le=65535)
    timeout_secs: int = Field(default=300, ge=1)
    kill_grace_secs: int = Field(default=10, ge=1)
    executions_per_benchmark: Literal[10, 15] = 10
    scheduler: SchedulerConfig = Field(default_factory=SchedulerConfig)
    model: str = "gpt-6-astra"
    reasoning_effort: str = "high"
    agent_timeout_secs: int = Field(default=300, ge=1)
    max_agent_actions: int = Field(default=100, ge=15)
    ranker_model: str | None = None

    @model_validator(mode="after")
    def unique_benchmarks(self):
        if len(set(self.benchmarks)) != len(self.benchmarks):
            raise ValueError("Benchmark paths must be unique")
        return self


class RunAction(StrictModel):
    action: Literal["RUN"] = "RUN"
    parent_run_id: str = Field(min_length=1)
    config_patch: ConfigPatch
    hypothesis: str = Field(min_length=1, max_length=4000)
    expected_signal: str = Field(min_length=1, max_length=4000)
    rationale: str = Field(min_length=1, max_length=4000)


class Filters(StrictModel):
    depth: int | None = Field(default=None, ge=0)
    refinement_step: int | None = Field(default=None, ge=0)
    rule: str | None = None


class AnalyzeAction(StrictModel):
    action: Literal["ANALYZE_PROFILE"] = "ANALYZE_PROFILE"
    run_id: str
    view: View
    filters: Filters = Field(default_factory=Filters)
    question: str = Field(min_length=1, max_length=4000)


class InspectAction(StrictModel):
    action: Literal["INSPECT_SOURCE"] = "INSPECT_SOURCE"
    mode: Literal["search", "read"]
    reason: str = Field(min_length=1, max_length=4000)
    query: str | None = Field(default=None, max_length=500)
    path: str | None = None
    start_line: int = Field(default=1, ge=1)
    end_line: int = Field(default=120, ge=1)

    @model_validator(mode="after")
    def valid_request(self):
        if self.mode == "search" and not self.query:
            raise ValueError("search requires query")
        if self.mode == "read" and (
            not self.path or not 0 <= self.end_line - self.start_line < 200
        ):
            raise ValueError("read requires path and a range of at most 200 lines")
        return self


class FinishAction(StrictModel):
    action: Literal["FINISH"] = "FINISH"
    rationale: str = Field(min_length=1, max_length=4000)


Action = Annotated[
    RunAction | AnalyzeAction | InspectAction | FinishAction, Field(discriminator="action")
]
ACTION_ADAPTER = TypeAdapter(Action)


class Findings(StrictModel):
    executive_summary: str
    baseline_behavior: str
    best_configuration: str
    profiling_diagnosis: str
    parameter_sensitivity: str
    implementation_recommendation: str
    confidence_and_unresolved_questions: str
    evidence_run_ids: list[str] = Field(min_length=1)


class Synthesis(StrictModel):
    overview: str
    recurring_recommendations: str
    benchmark_clusters: str
    configuration_patterns: str
    priorities_and_uncertainties: str
