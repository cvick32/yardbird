"""Render auditable research reports; mock reports clearly identify themselves."""

from pathlib import Path

from .models import Findings, Synthesis


def render_findings(benchmark_id: str, findings: Findings) -> str:
    headings = {
        "executive_summary": "Executive summary",
        "baseline_behavior": "Baseline behavior",
        "best_configuration": "Best configuration",
        "profiling_diagnosis": "Profiling diagnosis",
        "parameter_sensitivity": "Parameter sensitivity",
        "implementation_recommendation": "Primary implementation recommendation",
        "confidence_and_unresolved_questions": "Confidence / unresolved questions",
    }
    return (
        f"# Findings: {benchmark_id}\n\n"
        + "\n\n".join(
            f"## {heading}\n\n{getattr(findings, field)}" for field, heading in headings.items()
        )
        + "\n\nEvidence: "
        + ", ".join(findings.evidence_run_ids)
        + "\n"
    )


def save_findings(root: Path, benchmark_id: str, findings: Findings):
    text = render_findings(benchmark_id, findings)
    aggregate = root / "FINDINGS"
    aggregate.mkdir(exist_ok=True)
    for path in (
        aggregate / f"FINDINGS-{benchmark_id}.md",
        root / "benchmarks" / benchmark_id / f"FINDINGS-{benchmark_id}.md",
    ):
        with path.open("x") as stream:
            stream.write(text)


def render_synthesis(value: Synthesis) -> str:
    return (
        "# Cross-benchmark synthesis\n\n"
        + "\n\n".join(
            f"## {key.replace('_', ' ').capitalize()}\n\n{text}"
            for key, text in value.model_dump().items()
        )
        + "\n"
    )
