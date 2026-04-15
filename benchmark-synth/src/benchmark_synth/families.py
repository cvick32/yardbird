"""Family builders for semantic programs."""

from __future__ import annotations

from .ir import (
    Add,
    And,
    ArrayVar,
    Assignment,
    BenchmarkSpec,
    Difficulty,
    Eq,
    FamilyName,
    Ge,
    Gt,
    Implies,
    IntConst,
    Lt,
    PropertyFamily,
    PropertySpec,
    ScalarVar,
    Select,
    SemanticProgram,
    SkeletonType,
    Store,
    TransitionCase,
    VarRef,
    WitnessVar,
    validate_benchmark_spec,
)
from .naming import benchmark_name


def build_single_loop_copy(*, seed: int, ordinal: int, bug_flag: bool = False) -> BenchmarkSpec:
    arrays = (ArrayVar("a"), ArrayVar("b"))
    scalars = (
        ScalarVar("i", role="counter"),
        ScalarVar("n", role="bound"),
    )
    witnesses = (
        WitnessVar("Y"),
        WitnessVar("Z"),
    )

    init_constraints = (
        Eq(VarRef("i"), IntConst(0)),
        Ge(VarRef("n"), IntConst(2)),
    )

    write_index = Add(VarRef("i"), IntConst(1)) if bug_flag else VarRef("i")
    transition = TransitionCase(
        guard=Lt(VarRef("i"), VarRef("n")),
        assignments=(
            Assignment(
                "b",
                Store(VarRef("b"), write_index, Select(VarRef("a"), VarRef("i"))),
            ),
            Assignment("i", Add(VarRef("i"), IntConst(1))),
            Assignment("a", VarRef("a")),
            Assignment("n", VarRef("n")),
            Assignment("Y", VarRef("Y")),
            Assignment("Z", VarRef("Z")),
        ),
    )

    property_body = Implies(
        And(
            (
                Ge(VarRef("i"), VarRef("n")),
                Ge(VarRef("Y"), IntConst(0)),
                Gt(VarRef("Z"), VarRef("Y")),
                Lt(VarRef("Z"), VarRef("n")),
            )
        ),
        And(
            (
                Eq(Select(VarRef("b"), VarRef("Y")), Select(VarRef("a"), VarRef("Y"))),
                Eq(Select(VarRef("b"), VarRef("Z")), Select(VarRef("a"), VarRef("Z"))),
            )
        ),
    )
    property_spec = PropertySpec(
        family=PropertyFamily.POINTWISE,
        witness_names=("Y", "Z"),
        body=property_body,
    )

    spec = BenchmarkSpec(
        benchmark_name=benchmark_name(
            family=FamilyName.COPY.value,
            skeleton=SkeletonType.SINGLE_LOOP.value,
            property_family=PropertyFamily.POINTWISE.value,
            seed=seed,
            ordinal=ordinal,
            bug_flag=bug_flag,
        ),
        seed=seed,
        family_name=FamilyName.COPY,
        skeleton_type=SkeletonType.SINGLE_LOOP,
        property_family=PropertyFamily.POINTWISE,
        bug_flag=bug_flag,
        estimated_difficulty=Difficulty.EASY,
        program=SemanticProgram(
            arrays=arrays,
            scalars=scalars,
            witnesses=witnesses,
            init_constraints=init_constraints,
            transition_cases=(transition,),
            property_spec=property_spec,
        ),
    )
    validate_benchmark_spec(spec)
    return spec
