import asyncio
import sys

import pytest

from benchmark_investigator.artifacts import read_json, sha256
from benchmark_investigator.models import ExperimentConfig
from benchmark_investigator.runner import execute_run
from benchmark_investigator.summarizer import summarize_run


def run(binary, source_root, output, **kwargs):
    return asyncio.run(
        execute_run(
            directory=output,
            run_id="test-r01",
            benchmark_id="test",
            ordinal=1,
            binary=binary,
            binary_hash=sha256(binary),
            benchmark=source_root / "one.vmt",
            benchmark_hash=sha256(source_root / "one.vmt"),
            source_root=source_root,
            config=ExperimentConfig(),
            depth=2,
            timeout_secs=kwargs.pop("timeout_secs", 10),
            kill_grace_secs=1,
            **kwargs,
        )
    )


def test_nonzero_exit_retains_partial_json_and_immutable_directory(
    fake_binary, source_root, tmp_path
):
    fake_binary.write_text(
        fake_binary.read_text().replace("depth_limit", "refinement_limit") + "sys.exit(1)\n"
    )
    output = tmp_path / "run"
    metadata = run(fake_binary, source_root, output)
    assert metadata["returncode"] == 1
    assert metadata["termination_reason"] == "refinement_limit"
    assert metadata["z3_version"] == "fixture"
    assert read_json(output / "profile.json")["cost_records"]
    assert summarize_run(output)["outcome"]["profile_available"]
    with pytest.raises(FileExistsError):
        run(fake_binary, source_root, output)


def test_external_kill_returns_missing_profile_not_empty_success(
    fake_binary, source_root, tmp_path
):
    fake_binary.write_text(f"#!{sys.executable}\nimport time\ntime.sleep(20)\n")
    metadata = run(fake_binary, source_root, tmp_path / "run", timeout_secs=0)
    assert metadata["termination_reason"] == "external_timeout"
    assert metadata["wall_time_secs"] < 5
    assert read_json(tmp_path / "run/profile.json") is None
    assert not summarize_run(tmp_path / "run")["outcome"]["profile_available"]


def test_malformed_stdout_and_changed_binary(fake_binary, source_root, tmp_path):
    fake_binary.write_text(f"#!{sys.executable}\nprint('not JSON')\n")
    metadata = run(fake_binary, source_root, tmp_path / "run")
    assert metadata["termination_reason"] == "invalid_result"
    assert not metadata["profile_available"]


def test_cancellation_kills_process_and_records_interruption(fake_binary, source_root, tmp_path):
    fake_binary.write_text(f"#!{sys.executable}\nimport time\ntime.sleep(30)\n")
    output = tmp_path / "cancelled"

    async def scenario():
        task = asyncio.create_task(
            execute_run(
                directory=output,
                run_id="cancelled",
                benchmark_id="test",
                ordinal=1,
                binary=fake_binary,
                binary_hash=sha256(fake_binary),
                benchmark=source_root / "one.vmt",
                benchmark_hash=sha256(source_root / "one.vmt"),
                source_root=source_root,
                config=ExperimentConfig(),
                depth=2,
                timeout_secs=30,
                kill_grace_secs=1,
            )
        )
        await asyncio.sleep(0.1)
        task.cancel()
        with pytest.raises(asyncio.CancelledError):
            await task

    asyncio.run(scenario())
    metadata = read_json(output / "metadata.json")
    assert metadata["termination_reason"] == "interrupted"
    assert metadata["returncode"] is not None
