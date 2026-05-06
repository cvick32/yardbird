from benchmark_synth.families import (
    build_dual_counter_copy,
    build_single_loop_copy,
    build_single_loop_init,
    build_single_loop_transform,
    build_two_phase_transform,
)
from benchmark_synth.ir import validate_benchmark_spec


def test_single_loop_copy_has_multiple_witnesses() -> None:
    spec = build_single_loop_copy(seed=7, ordinal=0, bug_flag=False)
    validate_benchmark_spec(spec)

    assert len(spec.program.witnesses) == 2
    assert tuple(witness.name for witness in spec.program.witnesses) == ("Y", "Z")


def test_new_family_builders_validate() -> None:
    specs = [
        build_single_loop_init(seed=7, ordinal=1, bug_flag=False),
        build_single_loop_transform(seed=7, ordinal=2, bug_flag=False),
        build_dual_counter_copy(seed=7, ordinal=3, bug_flag=False),
        build_two_phase_transform(seed=7, ordinal=4, bug_flag=False),
    ]

    for spec in specs:
        validate_benchmark_spec(spec)
