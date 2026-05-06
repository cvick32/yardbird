"""Family builders for semantic programs."""

from __future__ import annotations

from collections.abc import Callable

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
    Le,
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


FamilyBuilder = Callable[[int, int, bool], BenchmarkSpec]


def supported_structures() -> dict[tuple[FamilyName, SkeletonType, PropertyFamily], FamilyBuilder]:
    return {
        (FamilyName.COPY, SkeletonType.SINGLE_LOOP, PropertyFamily.POINTWISE): build_single_loop_copy,
        (FamilyName.INIT, SkeletonType.SINGLE_LOOP, PropertyFamily.SEGMENT): build_single_loop_init,
        (
            FamilyName.TRANSFORM,
            SkeletonType.SINGLE_LOOP,
            PropertyFamily.POINTWISE,
        ): build_single_loop_transform,
        (FamilyName.COPY, SkeletonType.DUAL_COUNTER, PropertyFamily.POINTWISE): build_dual_counter_copy,
        (
            FamilyName.TRANSFORM,
            SkeletonType.TWO_PHASE,
            PropertyFamily.POINTWISE,
        ): build_two_phase_transform,
    }


def build_single_loop_copy(*, seed: int, ordinal: int, bug_flag: bool = False) -> BenchmarkSpec:
    arrays = (ArrayVar("a"), ArrayVar("b"))
    scalars = (ScalarVar("i", role="counter"), ScalarVar("n", role="bound"))
    witnesses = _common_witnesses()

    write_index = Add(VarRef("i"), IntConst(1)) if bug_flag else VarRef("i")
    transition = TransitionCase(
        guard=Lt(VarRef("i"), VarRef("n")),
        assignments=(
            Assignment("a", VarRef("a")),
            Assignment("b", Store(VarRef("b"), write_index, Select(VarRef("a"), VarRef("i")))),
            Assignment("i", Add(VarRef("i"), IntConst(1))),
            Assignment("n", VarRef("n")),
            Assignment("Y", VarRef("Y")),
            Assignment("Z", VarRef("Z")),
        ),
    )

    property = Implies(
        _ordered_witness_guard(done_guard=Ge(VarRef("i"), VarRef("n"))),
        And(
            (
                Eq(Select(VarRef("b"), VarRef("Y")), Select(VarRef("a"), VarRef("Y"))),
                Eq(Select(VarRef("b"), VarRef("Z")), Select(VarRef("a"), VarRef("Z"))),
            )
        ),
    )
    return _finalize_spec(
        benchmark_name_value=benchmark_name(
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
            init_constraints=_basic_init_constraints(),
            transition_cases=(transition,),
            property_spec=PropertySpec(
                family=PropertyFamily.POINTWISE,
                witness_names=("Y", "Z"),
                body=property,
            ),
        ),
    )


def build_single_loop_init(*, seed: int, ordinal: int, bug_flag: bool = False) -> BenchmarkSpec:
    arrays = (ArrayVar("a"),)
    scalars = (ScalarVar("i", role="counter"), ScalarVar("n", role="bound"))
    witnesses = _common_witnesses()

    write_index = Add(VarRef("i"), IntConst(1)) if bug_flag else VarRef("i")
    transition = TransitionCase(
        guard=Lt(VarRef("i"), VarRef("n")),
        assignments=(
            Assignment("a", Store(VarRef("a"), write_index, IntConst(0))),
            Assignment("i", Add(VarRef("i"), IntConst(1))),
            Assignment("n", VarRef("n")),
            Assignment("Y", VarRef("Y")),
            Assignment("Z", VarRef("Z")),
        ),
    )

    property = Implies(
        _ordered_witness_guard(done_guard=Ge(VarRef("i"), VarRef("n"))),
        And(
            (
                Eq(Select(VarRef("a"), VarRef("Y")), IntConst(0)),
                Eq(Select(VarRef("a"), VarRef("Z")), IntConst(0)),
            )
        ),
    )
    return _finalize_spec(
        benchmark_name_value=benchmark_name(
            family=FamilyName.INIT.value,
            skeleton=SkeletonType.SINGLE_LOOP.value,
            property_family=PropertyFamily.SEGMENT.value,
            seed=seed,
            ordinal=ordinal,
            bug_flag=bug_flag,
        ),
        seed=seed,
        family_name=FamilyName.INIT,
        skeleton_type=SkeletonType.SINGLE_LOOP,
        property_family=PropertyFamily.SEGMENT,
        bug_flag=bug_flag,
        estimated_difficulty=Difficulty.EASY,
        program=SemanticProgram(
            arrays=arrays,
            scalars=scalars,
            witnesses=witnesses,
            init_constraints=_basic_init_constraints(),
            transition_cases=(transition,),
            property_spec=PropertySpec(
                family=PropertyFamily.SEGMENT,
                witness_names=("Y", "Z"),
                body=property,
            ),
        ),
    )


def build_single_loop_transform(*, seed: int, ordinal: int, bug_flag: bool = False) -> BenchmarkSpec:
    arrays = (ArrayVar("a"), ArrayVar("b"))
    scalars = (ScalarVar("i", role="counter"), ScalarVar("n", role="bound"))
    witnesses = _common_witnesses()

    write_index = Add(VarRef("i"), IntConst(1)) if bug_flag else VarRef("i")
    transition = TransitionCase(
        guard=Lt(VarRef("i"), VarRef("n")),
        assignments=(
            Assignment("a", VarRef("a")),
            Assignment(
                "b",
                Store(
                    VarRef("b"),
                    write_index,
                    Add(Select(VarRef("a"), VarRef("i")), IntConst(1)),
                ),
            ),
            Assignment("i", Add(VarRef("i"), IntConst(1))),
            Assignment("n", VarRef("n")),
            Assignment("Y", VarRef("Y")),
            Assignment("Z", VarRef("Z")),
        ),
    )

    property = Implies(
        _ordered_witness_guard(done_guard=Ge(VarRef("i"), VarRef("n"))),
        And(
            (
                Eq(
                    Select(VarRef("b"), VarRef("Y")),
                    Add(Select(VarRef("a"), VarRef("Y")), IntConst(1)),
                ),
                Eq(
                    Select(VarRef("b"), VarRef("Z")),
                    Add(Select(VarRef("a"), VarRef("Z")), IntConst(1)),
                ),
            )
        ),
    )
    return _finalize_spec(
        benchmark_name_value=benchmark_name(
            family=FamilyName.TRANSFORM.value,
            skeleton=SkeletonType.SINGLE_LOOP.value,
            property_family=PropertyFamily.POINTWISE.value,
            seed=seed,
            ordinal=ordinal,
            bug_flag=bug_flag,
        ),
        seed=seed,
        family_name=FamilyName.TRANSFORM,
        skeleton_type=SkeletonType.SINGLE_LOOP,
        property_family=PropertyFamily.POINTWISE,
        bug_flag=bug_flag,
        estimated_difficulty=Difficulty.MEDIUM,
        program=SemanticProgram(
            arrays=arrays,
            scalars=scalars,
            witnesses=witnesses,
            init_constraints=_basic_init_constraints(),
            transition_cases=(transition,),
            property_spec=PropertySpec(
                family=PropertyFamily.POINTWISE,
                witness_names=("Y", "Z"),
                body=property,
            ),
        ),
    )


def build_dual_counter_copy(*, seed: int, ordinal: int, bug_flag: bool = False) -> BenchmarkSpec:
    arrays = (ArrayVar("a"), ArrayVar("b"))
    scalars = (
        ScalarVar("i", role="left_counter"),
        ScalarVar("j", role="right_counter"),
        ScalarVar("n", role="bound"),
    )
    witnesses = _common_witnesses()

    right_index = Add(VarRef("j"), IntConst(1)) if bug_flag else VarRef("j")
    transition = TransitionCase(
        guard=Le(VarRef("i"), VarRef("j")),
        assignments=(
            Assignment("a", VarRef("a")),
            Assignment(
                "b",
                Store(
                    Store(VarRef("b"), VarRef("i"), Select(VarRef("a"), VarRef("i"))),
                    right_index,
                    Select(VarRef("a"), VarRef("j")),
                ),
            ),
            Assignment("i", Add(VarRef("i"), IntConst(1))),
            Assignment("j", Add(VarRef("j"), IntConst(-1))),
            Assignment("n", VarRef("n")),
            Assignment("Y", VarRef("Y")),
            Assignment("Z", VarRef("Z")),
        ),
    )

    property = Implies(
        _ordered_witness_guard(done_guard=Gt(VarRef("i"), VarRef("j"))),
        And(
            (
                Eq(Select(VarRef("b"), VarRef("Y")), Select(VarRef("a"), VarRef("Y"))),
                Eq(Select(VarRef("b"), VarRef("Z")), Select(VarRef("a"), VarRef("Z"))),
            )
        ),
    )
    return _finalize_spec(
        benchmark_name_value=benchmark_name(
            family=FamilyName.COPY.value,
            skeleton=SkeletonType.DUAL_COUNTER.value,
            property_family=PropertyFamily.POINTWISE.value,
            seed=seed,
            ordinal=ordinal,
            bug_flag=bug_flag,
        ),
        seed=seed,
        family_name=FamilyName.COPY,
        skeleton_type=SkeletonType.DUAL_COUNTER,
        property_family=PropertyFamily.POINTWISE,
        bug_flag=bug_flag,
        estimated_difficulty=Difficulty.HARD,
        program=SemanticProgram(
            arrays=arrays,
            scalars=scalars,
            witnesses=witnesses,
            init_constraints=(
                Eq(VarRef("i"), IntConst(0)),
                Eq(VarRef("j"), Add(VarRef("n"), IntConst(-1))),
                Ge(VarRef("n"), IntConst(3)),
            ),
            transition_cases=(transition,),
            property_spec=PropertySpec(
                family=PropertyFamily.POINTWISE,
                witness_names=("Y", "Z"),
                body=property,
            ),
        ),
    )


def build_two_phase_transform(*, seed: int, ordinal: int, bug_flag: bool = False) -> BenchmarkSpec:
    arrays = (ArrayVar("a"), ArrayVar("b"))
    scalars = (
        ScalarVar("i", role="counter"),
        ScalarVar("n", role="bound"),
        ScalarVar("pc", role="phase"),
    )
    witnesses = _common_witnesses()

    phase_one_write_index = Add(VarRef("i"), IntConst(1)) if bug_flag else VarRef("i")

    phase_zero_step = TransitionCase(
        guard=And((Eq(VarRef("pc"), IntConst(0)), Lt(VarRef("i"), VarRef("n")))),
        assignments=(
            Assignment("a", VarRef("a")),
            Assignment("b", Store(VarRef("b"), VarRef("i"), Select(VarRef("a"), VarRef("i")))),
            Assignment("i", Add(VarRef("i"), IntConst(1))),
            Assignment("n", VarRef("n")),
            Assignment("pc", VarRef("pc")),
            Assignment("Y", VarRef("Y")),
            Assignment("Z", VarRef("Z")),
        ),
    )
    phase_switch = TransitionCase(
        guard=And((Eq(VarRef("pc"), IntConst(0)), Ge(VarRef("i"), VarRef("n")))),
        assignments=(
            Assignment("a", VarRef("a")),
            Assignment("b", VarRef("b")),
            Assignment("i", IntConst(0)),
            Assignment("n", VarRef("n")),
            Assignment("pc", IntConst(1)),
            Assignment("Y", VarRef("Y")),
            Assignment("Z", VarRef("Z")),
        ),
    )
    phase_one_step = TransitionCase(
        guard=And((Eq(VarRef("pc"), IntConst(1)), Lt(VarRef("i"), VarRef("n")))),
        assignments=(
            Assignment("a", VarRef("a")),
            Assignment(
                "b",
                Store(
                    VarRef("b"),
                    phase_one_write_index,
                    Add(Select(VarRef("b"), VarRef("i")), IntConst(1)),
                ),
            ),
            Assignment("i", Add(VarRef("i"), IntConst(1))),
            Assignment("n", VarRef("n")),
            Assignment("pc", VarRef("pc")),
            Assignment("Y", VarRef("Y")),
            Assignment("Z", VarRef("Z")),
        ),
    )
    done_stutter = TransitionCase(
        guard=And((Eq(VarRef("pc"), IntConst(1)), Ge(VarRef("i"), VarRef("n")))),
        assignments=(
            Assignment("a", VarRef("a")),
            Assignment("b", VarRef("b")),
            Assignment("i", VarRef("i")),
            Assignment("n", VarRef("n")),
            Assignment("pc", VarRef("pc")),
            Assignment("Y", VarRef("Y")),
            Assignment("Z", VarRef("Z")),
        ),
    )

    property = Implies(
        _ordered_witness_guard(
            done_guard=And((Eq(VarRef("pc"), IntConst(1)), Ge(VarRef("i"), VarRef("n"))))
        ),
        And(
            (
                Eq(
                    Select(VarRef("b"), VarRef("Y")),
                    Add(Select(VarRef("a"), VarRef("Y")), IntConst(1)),
                ),
                Eq(
                    Select(VarRef("b"), VarRef("Z")),
                    Add(Select(VarRef("a"), VarRef("Z")), IntConst(1)),
                ),
            )
        ),
    )
    return _finalize_spec(
        benchmark_name_value=benchmark_name(
            family=FamilyName.TRANSFORM.value,
            skeleton=SkeletonType.TWO_PHASE.value,
            property_family=PropertyFamily.POINTWISE.value,
            seed=seed,
            ordinal=ordinal,
            bug_flag=bug_flag,
        ),
        seed=seed,
        family_name=FamilyName.TRANSFORM,
        skeleton_type=SkeletonType.TWO_PHASE,
        property_family=PropertyFamily.POINTWISE,
        bug_flag=bug_flag,
        estimated_difficulty=Difficulty.HARD,
        program=SemanticProgram(
            arrays=arrays,
            scalars=scalars,
            witnesses=witnesses,
            init_constraints=(
                Eq(VarRef("i"), IntConst(0)),
                Eq(VarRef("pc"), IntConst(0)),
                Ge(VarRef("n"), IntConst(2)),
            ),
            transition_cases=(phase_zero_step, phase_switch, phase_one_step, done_stutter),
            property_spec=PropertySpec(
                family=PropertyFamily.POINTWISE,
                witness_names=("Y", "Z"),
                body=property,
            ),
        ),
    )


def _common_witnesses() -> tuple[WitnessVar, WitnessVar]:
    return (WitnessVar("Y"), WitnessVar("Z"))


def _basic_init_constraints() -> tuple[Eq | Ge, ...]:
    return (Eq(VarRef("i"), IntConst(0)), Ge(VarRef("n"), IntConst(2)))


def _ordered_witness_guard(*, done_guard) -> And:
    return And((done_guard, Ge(VarRef("Y"), IntConst(0)), Gt(VarRef("Z"), VarRef("Y")), Lt(VarRef("Z"), VarRef("n"))))


def _finalize_spec(
    *,
    benchmark_name_value: str,
    seed: int,
    family_name: FamilyName,
    skeleton_type: SkeletonType,
    property_family: PropertyFamily,
    bug_flag: bool,
    estimated_difficulty: Difficulty,
    program: SemanticProgram,
) -> BenchmarkSpec:
    spec = BenchmarkSpec(
        benchmark_name=benchmark_name_value,
        seed=seed,
        family_name=family_name,
        skeleton_type=skeleton_type,
        property_family=property_family,
        bug_flag=bug_flag,
        estimated_difficulty=estimated_difficulty,
        program=program,
    )
    validate_benchmark_spec(spec)
    return spec
