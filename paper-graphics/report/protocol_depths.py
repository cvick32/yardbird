"""Completed-depth comparison for distributed-protocol VMT inputs only."""

from pathlib import PurePosixPath

from report.typst import typst_cell, typst_table
from src.benchmark_parsing import BenchmarkResult


def depth_cell(result: BenchmarkResult | None) -> str:
    if result is None:
        return "missing"
    progress = result.run_progress
    depth = "?"
    if isinstance(progress, dict) and "deepest_completed_depth" in progress:
        completed = progress["deepest_completed_depth"]
        depth = "none" if completed is None else str(completed)
    reason = progress.get("termination_reason") if isinstance(progress, dict) else None
    outcome = {
        "depth_limit": "OK", "proof": "PROOF", "timeout": "T",
        "counterexample": "CEX", "solver_unknown": "UNK",
    }.get(reason, {
        "Success": "OK", "_FoundProof": "PROOF", "Timeout": "T",
    }.get(result.result_type, "ERR"))
    if outcome in {"CEX", "UNK"} and progress.get("current_depth") is not None:
        outcome += f"@{progress['current_depth']}"
    return f"{depth} ({outcome})"


def protocol_depth_sections(
    grouped: dict[str, dict[str, BenchmarkResult]],
) -> list[str]:
    protocols = {
        name: results for name, results in grouped.items()
        if "/examples/distributed_protocols/" in "/" + name.replace("\\", "/")
        and PurePosixPath(name.replace("\\", "/")).suffix.lower() == ".vmt"
    }
    if not protocols:
        return []
    representatives = {
        key: result for results in protocols.values() for key, result in results.items()
    }
    keys = sorted(representatives, key=lambda key: (
        representatives[key].strategy != "concrete", key,
    ))
    lines = []
    # Keep every benchmark visible even when the policy matrix is wide.
    for start in range(0, len(keys), 4):
        page_keys = keys[start:start + 4]
        headers = ["Benchmark"] + [f"S{keys.index(key) + 1}" for key in page_keys]
        lines.extend([
            "#pagebreak()", "", "= Distributed Protocol Completed Depths", "",
            "Largest completed zero-based BMC depth, not the attempted depth. "
            "For target 20, depth 19 completes checks 0-19. These are bounded checks.", "",
            typst_cell("OK = completed bound; T = timeout; CEX/UNK@k = counterexample/unknown "
            "at depth k; PROOF = proof found; ERR = other failure. "
            "none = no completed depth; ? = progress unavailable; missing = no result.")[1:-1], "",
        ])
        for key in page_keys:
            label = f"S{keys.index(key) + 1}: {representatives[key].get_display_name()}"
            lines.extend([typst_cell(label)[1:-1], ""])
        rows = []
        for name, results in sorted(protocols.items()):
            relative = name.replace("\\", "/").split("examples/distributed_protocols/", 1)[1]
            # Keep the encoding suffix and family to distinguish source/companion inputs.
            label = relative.removesuffix(".vmt")
            family, _, filename = label.rpartition("/")
            if filename == family or filename == family + ".encoding":
                label = filename
            rows.append([label] + [depth_cell(results.get(key)) for key in page_keys])
        lines.extend([typst_table(
            headers, rows, columns="(" + ", ".join(["2.6fr"] + ["1fr"] * len(page_keys)) + ")",
        ), ""])
    return lines
