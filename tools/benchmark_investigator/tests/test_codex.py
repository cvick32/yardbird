from benchmark_investigator.codex_backend import CodexCLIBackend, DecisionEnvelope, strict_schema


def test_codex_command_disables_execution_and_uses_configured_model(tmp_path):
    import sys

    command = CodexCLIBackend("gpt-6-astra", executable=sys.executable).command(tmp_path)
    assert command[command.index("--sandbox") + 1] == "read-only"
    assert command[command.index("--model") + 1] == "gpt-6-astra"
    assert "--ignore-user-config" in command
    for feature in ("shell_tool", "plugins", "apps", "multi_agent"):
        i = command.index(feature)
        assert command[i - 1] == "--disable"
    assert "--output-schema" in command


def test_schema_is_strict_object_with_union_nested_below_root():
    schema = strict_schema(DecisionEnvelope)
    assert schema["type"] == "object"

    def check(value):
        if isinstance(value, dict):
            assert "default" not in value
            assert "discriminator" not in value
            if value.get("type") == "object":
                assert value["additionalProperties"] is False
                assert set(value["required"]) == set(value["properties"])
            for item in value.values():
                check(item)
        elif isinstance(value, list):
            for item in value:
                check(item)

    check(schema)


def test_codex_discovers_desktop_binary_without_path(monkeypatch, tmp_path):
    from benchmark_investigator import codex_backend

    binary = tmp_path / "desktop-codex"
    binary.write_text("#!/bin/sh\nexit 0\n")
    binary.chmod(0o755)
    monkeypatch.delenv("CODEX_EXECUTABLE", raising=False)
    monkeypatch.setenv("PATH", "")
    monkeypatch.setattr(codex_backend, "DESKTOP_CODEX_PATHS", (binary,))
    assert CodexCLIBackend("gpt-6-astra").executable == str(binary)


def test_codex_explicit_override_does_not_silently_fallback(monkeypatch, tmp_path):
    import sys

    import pytest

    monkeypatch.setenv("CODEX_EXECUTABLE", sys.executable)
    assert CodexCLIBackend("gpt-6-astra").executable == sys.executable
    with pytest.raises(ValueError, match="CODEX_EXECUTABLE"):
        CodexCLIBackend("gpt-6-astra", executable=str(tmp_path / "missing"))


def test_missing_codex_fails_before_campaign_runs(monkeypatch, fake_binary, source_root, tmp_path):
    import asyncio

    import pytest

    from benchmark_investigator import cli, codex_backend
    from benchmark_investigator.campaign import create_campaign
    from benchmark_investigator.models import CampaignConfig

    campaign = create_campaign(
        source_root, tmp_path / "campaign", CampaignConfig(benchmarks=["one.vmt"]), fake_binary
    )
    monkeypatch.delenv("CODEX_EXECUTABLE", raising=False)
    monkeypatch.setattr(codex_backend.shutil, "which", lambda executable: None)
    monkeypatch.setattr(codex_backend, "DESKTOP_CODEX_PATHS", ())
    args = cli.parser().parse_args(["campaign", str(campaign.directory)])
    with pytest.raises(ValueError, match="CODEX_EXECUTABLE"):
        asyncio.run(cli.dispatch(args))
    assert not campaign.runs(next(iter(campaign.benchmarks)))
    # Baseline-only work does not require a model executable.
    monkeypatch.undo()
    monkeypatch.setenv("CODEX_EXECUTABLE", str(tmp_path / "missing"))
    args.baselines_only = True
    asyncio.run(cli.dispatch(args))
    assert len(campaign.runs(next(iter(campaign.benchmarks)))) == 2
