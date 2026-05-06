"""Typed semantic IR for benchmark generation."""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum

from .metadata import BenchmarkMetadata


GENERATOR_VERSION = "0.1.0"


class SkeletonType(StrEnum):
    SINGLE_LOOP = "single_loop"
    TWO_PHASE = "two_phase"
    DUAL_COUNTER = "dual_counter"
    NESTED = "nested"


class FamilyName(StrEnum):
    COPY = "copy"
    INIT = "init"
    TRANSFORM = "transform"
    SCAN = "scan"
    SUMMARY = "summary"
    NESTED = "nested"


class PropertyFamily(StrEnum):
    POINTWISE = "pointwise"
    PREFIX = "prefix"
    SEGMENT = "segment"
    SUMMARY = "summary"
    PHASE = "phase"


class Difficulty(StrEnum):
    EASY = "easy"
    MEDIUM = "medium"
    HARD = "hard"


class BugKind(StrEnum):
    WRONG_WRITE_INDEX = "wrong_write_index"


class Sort(StrEnum):
    INT = "Int"
    ARRAY_INT_INT = "(Array Int Int)"


@dataclass(frozen=True)
class ArrayVar:
    name: str
    sort: Sort = Sort.ARRAY_INT_INT


@dataclass(frozen=True)
class ScalarVar:
    name: str
    sort: Sort = Sort.INT
    role: str = "state"


@dataclass(frozen=True)
class WitnessVar:
    name: str
    sort: Sort = Sort.INT
    role: str = "witness"


@dataclass(frozen=True)
class Expr:
    """Marker base class for typed expressions."""


@dataclass(frozen=True)
class VarRef(Expr):
    name: str


@dataclass(frozen=True)
class IntConst(Expr):
    value: int


@dataclass(frozen=True)
class Add(Expr):
    left: Expr
    right: Expr


@dataclass(frozen=True)
class Select(Expr):
    array: Expr
    index: Expr


@dataclass(frozen=True)
class Store(Expr):
    array: Expr
    index: Expr
    value: Expr


@dataclass(frozen=True)
class Eq(Expr):
    left: Expr
    right: Expr


@dataclass(frozen=True)
class Lt(Expr):
    left: Expr
    right: Expr


@dataclass(frozen=True)
class Le(Expr):
    left: Expr
    right: Expr


@dataclass(frozen=True)
class Gt(Expr):
    left: Expr
    right: Expr


@dataclass(frozen=True)
class Ge(Expr):
    left: Expr
    right: Expr


@dataclass(frozen=True)
class Or(Expr):
    terms: tuple[Expr, ...]


@dataclass(frozen=True)
class And(Expr):
    terms: tuple[Expr, ...]


@dataclass(frozen=True)
class Implies(Expr):
    antecedent: Expr
    consequent: Expr


@dataclass(frozen=True)
class Assignment:
    target: str
    expr: Expr


@dataclass(frozen=True)
class TransitionCase:
    guard: Expr
    assignments: tuple[Assignment, ...]


@dataclass(frozen=True)
class NestedLoop:
    loop_var: str
    lower_bound: Expr
    upper_bound: Expr
    body: tuple["NestedLoop", ...] = ()


@dataclass(frozen=True)
class PropertySpec:
    family: PropertyFamily
    witness_names: tuple[str, ...]
    body: Expr


@dataclass(frozen=True)
class SemanticProgram:
    arrays: tuple[ArrayVar, ...]
    scalars: tuple[ScalarVar, ...]
    witnesses: tuple[WitnessVar, ...]
    init_constraints: tuple[Expr, ...]
    transition_cases: tuple[TransitionCase, ...]
    property_spec: PropertySpec
    loop_tree: tuple[NestedLoop, ...] = ()


@dataclass(frozen=True)
class BenchmarkSpec:
    benchmark_name: str
    seed: int
    family_name: FamilyName
    skeleton_type: SkeletonType
    property_family: PropertyFamily
    bug_flag: bool
    estimated_difficulty: Difficulty
    program: SemanticProgram

    def metadata(self) -> BenchmarkMetadata:
        return BenchmarkMetadata(
            family_name=self.family_name.value,
            skeleton_type=self.skeleton_type.value,
            property_family=self.property_family.value,
            bug_flag=self.bug_flag,
            estimated_difficulty=self.estimated_difficulty.value,
            generator_version=GENERATOR_VERSION,
            seed=self.seed,
            benchmark_name=self.benchmark_name,
        )


def all_state_var_names(program: SemanticProgram) -> list[str]:
    return [var.name for var in program.arrays + program.scalars + program.witnesses]


def validate_benchmark_spec(spec: BenchmarkSpec) -> None:
    program = spec.program
    if not program.arrays:
        raise ValueError("program must contain at least one array")
    if not program.scalars:
        raise ValueError("program must contain at least one scalar")
    if len(program.witnesses) < 2:
        raise ValueError("program must contain at least two witness variables")
    if not program.transition_cases:
        raise ValueError("program must contain at least one transition case")
    if spec.property_family != program.property_spec.family:
        raise ValueError("benchmark and property families do not match")

    names = all_state_var_names(program)
    if len(set(names)) != len(names):
        raise ValueError("state variable names must be unique")

    missing_witnesses = set(program.property_spec.witness_names) - {
        witness.name for witness in program.witnesses
    }
    if missing_witnesses:
        raise ValueError(f"property references unknown witnesses: {sorted(missing_witnesses)}")

    state_names = set(all_state_var_names(program))
    for case in program.transition_cases:
        assigned_names = [assignment.target for assignment in case.assignments]
        if len(set(assigned_names)) != len(assigned_names):
            raise ValueError("transition case assigns the same target more than once")
        if set(assigned_names) != state_names:
            missing = sorted(state_names - set(assigned_names))
            extra = sorted(set(assigned_names) - state_names)
            raise ValueError(
                "transition case must assign every state variable exactly once; "
                f"missing={missing}, extra={extra}"
            )
