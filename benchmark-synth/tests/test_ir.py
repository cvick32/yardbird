from benchmark_synth.families import build_single_loop_copy
from benchmark_synth.ir import validate_benchmark_spec


def test_single_loop_copy_has_multiple_witnesses() -> None:
    spec = build_single_loop_copy(seed=7, ordinal=0, bug_flag=False)
    validate_benchmark_spec(spec)

    assert len(spec.program.witnesses) == 2
    assert tuple(witness.name for witness in spec.program.witnesses) == ("Y", "Z")
