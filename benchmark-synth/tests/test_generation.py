import json

from benchmark_synth.generate import GenerateConfig, generate_corpus
from benchmark_synth.ir import FamilyName, PropertyFamily, SkeletonType


def test_generate_corpus_writes_benchmarks_and_metadata(tmp_path) -> None:
    output_dir = tmp_path / "dev"
    manifest = generate_corpus(
        GenerateConfig(
            output_dir=output_dir,
            seed=5,
            count=4,
            family=FamilyName.COPY,
            skeleton=SkeletonType.SINGLE_LOOP,
            property_family=PropertyFamily.POINTWISE,
            bug_ratio=1.0,
        )
    )

    assert len(manifest.entries) == 4
    assert any(entry.bug_flag for entry in manifest.entries)

    manifest_path = output_dir / "manifest.json"
    assert manifest_path.exists()
    payload = json.loads(manifest_path.read_text())
    assert len(payload["entries"]) == 4


def test_generate_mixed_corpus_uses_multiple_structures(tmp_path) -> None:
    output_dir = tmp_path / "mixed"
    manifest = generate_corpus(
        GenerateConfig(
            output_dir=output_dir,
            seed=17,
            count=20,
            bug_ratio=0.25,
        )
    )

    metadata_payloads = [
        json.loads((output_dir / "metadata" / f"{entry.benchmark_name}.json").read_text())
        for entry in manifest.entries
    ]
    families = {payload["family_name"] for payload in metadata_payloads}
    skeletons = {payload["skeleton_type"] for payload in metadata_payloads}

    assert len(families) >= 3
    assert len(skeletons) >= 2
