from benchmark_synth.families import build_single_loop_copy, build_two_phase_transform
from benchmark_synth.lower_vmt import lower_benchmark


def test_lowered_vmt_has_no_let_and_declares_witnesses() -> None:
    spec = build_single_loop_copy(seed=7, ordinal=0, bug_flag=False)
    lowered = lower_benchmark(spec)

    assert "(let " not in lowered.vmt_text
    assert "(declare-fun Y () Int)" in lowered.vmt_text
    assert "(declare-fun Z () Int)" in lowered.vmt_text
    assert "(select b Y)" in lowered.vmt_text
    assert "(select b Z)" in lowered.vmt_text


def test_two_phase_lowering_contains_guard_cover_and_implications() -> None:
    spec = build_two_phase_transform(seed=7, ordinal=0, bug_flag=False)
    lowered = lower_benchmark(spec)

    assert "(declare-fun pc () Int)" in lowered.vmt_text
    assert "(or " in lowered.vmt_text
    assert "(=> " in lowered.vmt_text
