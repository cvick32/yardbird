import pytest
from benchmark_synth.families import build_single_loop_copy
from benchmark_synth.metadata import BenchmarkMetadata
from benchmark_synth.validate import normalized_vmt_hash, validate_structural


def test_metadata_rejects_unknown_fields() -> None:
    with pytest.raises(ValueError):
        BenchmarkMetadata.from_dict(
            {
                "family_name": "copy",
                "skeleton_type": "single_loop",
                "property_family": "pointwise",
                "bug_flag": False,
                "estimated_difficulty": "easy",
                "generator_version": "0.1.0",
                "seed": 7,
                "benchmark_name": "x",
                "hidden_hint": "should_not_be_allowed",
            }
        )


def test_normalized_vmt_hash_is_stable_for_same_spec() -> None:
    spec = build_single_loop_copy(seed=9, ordinal=0, bug_flag=False)
    validate_structural(spec)

    assert normalized_vmt_hash(spec) == normalized_vmt_hash(spec)
