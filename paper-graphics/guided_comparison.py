"""Render instantiation comparisons, including running snapshots.

Run with this project's Python environment. Inputs are Garden JSON files or
main_eval run.json manifests. Re-running replaces figures, never raw evidence.
"""

from __future__ import annotations

import argparse
import csv
import json
from collections import Counter
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


METHODS = ("jev", "jev-fallback", "openai", "yardbird", "z3")
GUIDED = {"jev", "jev-fallback", "openai"}
LABELS = {"jev": "JEV", "jev-fallback": "JEV + Yardbird", "openai": "OpenAI Astra",
          "yardbird": "Yardbird abstract", "z3": "Z3 arrays"}
SOLVED = {"Success", "_FoundProof"}
TOKEN_FIELDS = (
    "input_tokens", "cached_input_tokens", "short_cache_write_tokens",
    "long_cache_write_tokens", "uncached_input_tokens", "output_tokens",
)


def read_events(path: Path) -> list[dict]:
    if not path.exists():
        return []
    lines = path.read_bytes().splitlines(keepends=True)
    events = []
    for index, line in enumerate(lines):
        try:
            events.append(json.loads(line))
        except json.JSONDecodeError:
            # A worker may be writing the final record during S3 sync.
            if index != len(lines) - 1 or line.endswith(b"\n"):
                raise
    return events


def api_metrics(events: list[dict]) -> dict:
    """Each cost-bearing record represents one call, never sum run_cost totals."""
    calls = [e for e in events if isinstance(e.get("cost"), dict)]
    # A killed/in-flight request has no response/cost record; do not report free.
    answered = {e.get("query_id") for e in calls}
    skipped = {e.get("query_id") for e in events if e["event"] == "request_skipped"}
    unresolved = {e.get("query_id") for e in events if e["event"] == "request"} - answered - skipped
    costs = [e["cost"].get("estimated_usd") for e in calls]
    unknown = sum(c is None for c in costs) + len(unresolved)
    episodes = [e for e in events if e["event"] == "episode_end"]
    accepted = sum(e.get("outcome") == "violated" for e in episodes)
    metrics = {
        "api_calls": len(calls) + len(unresolved),
        "unknown_cost_calls": unknown,
        "estimated_subtotal_usd": sum(c for c in costs if c is not None),
        "api_seconds": sum(e.get("elapsed_secs", 0) for e in calls),
        "episodes": len(episodes),
        "accepted_episodes": accepted,
        "fallback_episodes": sum(bool(e.get("ordinary_fallback")) for e in episodes),
        "dry_run": any(e.get("outcome") == "dry_run" for e in events),
        "resolved_models": ";".join(sorted({str(e.get("resolved_model") or e.get("response", {}).get("model"))
                                           for e in calls if e.get("resolved_model") or e.get("response", {}).get("model")})),
    }
    metrics["estimated_total_usd"] = None if unknown else metrics["estimated_subtotal_usd"]
    for field in TOKEN_FIELDS:
        metrics[field] = sum((e["cost"].get("tokens") or e["cost"]).get(field) or 0 for e in calls)
    return metrics


def suite_paths(inputs: list[Path]) -> list[Path]:
    paths = []
    for path in inputs:
        payload = json.loads(path.read_text())
        if "subruns" in payload:
            paths.extend(Path(s["result_path"]) for s in payload["subruns"] if Path(s["result_path"]).exists())
        else:
            paths.append(path)
    return list(dict.fromkeys(paths))


def collect(inputs: list[Path]) -> tuple[list[dict], list[dict]]:
    rows = {}
    for path in suite_paths(inputs):
        suite = json.loads(path.read_text())
        metadata = suite["metadata"]
        runs, examples = metadata["planned_runs"], metadata["examples"]
        observed = {(r["run_name"], b["example"]): r for b in suite["benchmarks"] for r in b["result"]}
        for run_index, run in enumerate(runs):
            method = run.split("_d", 1)[0]
            if method not in METHODS:
                raise ValueError(f"Unknown comparison method: {run}")
            for example_index, example in enumerate(examples):
                key = (method, example)
                if key in rows:
                    raise ValueError(f"Duplicate method/benchmark; pass one trial at a time: {key}")
                result = observed.get((run, example), {})
                outcome = result.get("result", {"Pending": None})
                status, payload = next(iter(outcome.items()))
                payload = payload if isinstance(payload, dict) else {}
                progress = result.get("run_progress") or payload.get("run_progress") or {}
                embedded = result.get("api_usage")
                if isinstance(embedded, dict):
                    # Embedded accounting is authoritative, including null totals.
                    # Figures work with results.json alone and do not re-read logs.
                    api = {key: embedded.get(key, default) for key, default in api_metrics([]).items()}
                    models = embedded.get("resolved_models", [])
                    api["resolved_models"] = ";".join(models) if isinstance(models, list) else models
                    log_available = embedded.get("log_available", False)
                    evidence_available = True
                    usage_source = "embedded"
                else:
                    # Compatibility for old results and still-running benchmarks.
                    log = path.with_suffix(".api") / f"{run_index:04}-{example_index:04}.jsonl"
                    if not log.exists():
                        original = result.get("llm" if method == "openai" else "decision_model", {}).get(
                            "llm_log" if method == "openai" else "jev_log")
                        if original:
                            log = Path(original)
                    events = read_events(log) if method in GUIDED else []
                    api = api_metrics(events)
                    log_available = bool(events)
                    evidence_available = bool(events) or method not in GUIDED
                    usage_source = "jsonl" if events else "none"
                    if not evidence_available:
                        api["estimated_total_usd"] = None
                depth = progress.get("deepest_completed_depth")
                row = {
                    "method": method, "example": example, "status": status,
                    "target_depth": result.get("depth"), "runtime_seconds": result.get("run_time", 0) / 1000,
                    "completed_depths": depth + 1 if depth is not None else 0,
                    "instantiations": payload.get("total_instantiations_added", 0),
                    "no_guided_fallback": result.get("no_guided_fallback"),
                    "api_log_available": log_available,
                    "api_evidence_available": evidence_available,
                    "api_usage_source": usage_source, **api,
                }
                rows[key] = row
    summaries = []
    for method in METHODS:
        selected = [r for r in rows.values() if r["method"] == method]
        if not selected:
            continue
        summary = {"method": method, "planned": len(selected), "completed": sum(r["status"] != "Pending" for r in selected),
                   "solved": sum(r["status"] in SOLVED for r in selected)}
        for field in ("api_calls", "unknown_cost_calls", "estimated_subtotal_usd", "api_seconds",
                      "episodes", "accepted_episodes", "fallback_episodes", *TOKEN_FIELDS):
            summary[field] = sum(r[field] for r in selected)
        summary["estimated_total_usd"] = (summary["estimated_subtotal_usd"]
                                          if all(r["estimated_total_usd"] is not None for r in selected) else None)
        summary["missing_api_evidence"] = sum(not r["api_evidence_available"] for r in selected) if method in GUIDED else 0
        summary["incomplete_accounting_runs"] = sum(r["estimated_total_usd"] is None for r in selected)
        summary["dry_run"] = any(r["dry_run"] for r in selected)
        summary["acceptance_rate"] = summary["accepted_episodes"] / summary["episodes"] if summary["episodes"] else None
        accepted = summary["accepted_episodes"]
        summary["usd_per_accepted_episode"] = (summary["estimated_total_usd"] / accepted
                                               if accepted and summary["estimated_total_usd"] is not None else None)
        summary["api_seconds_per_accepted_episode"] = summary["api_seconds"] / accepted if accepted else None
        summaries.append(summary)
    return list(rows.values()), summaries


def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open("w", newline="") as output:
        if rows:
            writer = csv.DictWriter(output, fieldnames=list(rows[0]))
            writer.writeheader()
            writer.writerows(rows)


def render(inputs: list[Path], output: Path) -> None:
    rows, summaries = collect(inputs)
    output.mkdir(parents=True, exist_ok=True)
    write_csv(output / "benchmarks.csv", rows)
    write_csv(output / "summary.csv", summaries)
    (output / "summary.json").write_text(json.dumps(summaries, indent=2) + "\n")
    dry_run = any(s["dry_run"] for s in summaries)
    partial = any(s["completed"] < s["planned"] for s in summaries)
    note = "DRY RUN — pipeline check" if dry_run else "Partial results" if partial else "Single-trial evaluation"

    def save(fig, name):
        fig.suptitle(note)
        fig.tight_layout()
        fig.savefig(output / f"{name}.pdf")
        fig.savefig(output / f"{name}.png", dpi=160)
        plt.close(fig)

    methods = [s["method"] for s in summaries]
    labels = [LABELS[m] for m in methods]
    guided = [s for s in summaries if s["method"] in GUIDED]
    guided_labels = [LABELS[s["method"]] for s in guided]
    fig, ax = plt.subplots(figsize=(9, 4))
    bottom = [0] * len(methods)
    statuses = ("Success", "_FoundProof", "NoProgress", "Timeout", "Failed", "Error", "Pending")
    for status in statuses:
        values = [sum(r["method"] == method and r["status"] == status for r in rows) for method in methods]
        if any(values):
            ax.bar(labels, values, bottom=bottom, label=status)
            bottom = [a + b for a, b in zip(bottom, values)]
    ax.set_ylabel("Benchmarks")
    ax.legend(fontsize=8)
    save(fig, "outcomes")

    for name, field, ylabel, solved_only in [
        ("runtime_cactus", "runtime_seconds", "End-to-end runtime (seconds)", True),
        ("instantiation_cactus", "instantiations", "Installed instances", True),
        ("depth_progress", "completed_depths", "Completed BMC depths", False),
    ]:
        fig, ax = plt.subplots(figsize=(7, 4))
        for method, label in zip(methods, labels):
            values = sorted(r[field] for r in rows if r["method"] == method and
                            (r["status"] in SOLVED if solved_only else r["status"] != "Pending"))
            ax.plot(range(1, len(values) + 1), values, label=label, marker=".")
        ax.set(xlabel="Benchmarks (sorted independently)", ylabel=ylabel)
        ax.legend(fontsize=8)
        save(fig, name)

    fig, axes = plt.subplots(1, 3, figsize=(12, 4))
    for ax, field, label in zip(axes, ("estimated_subtotal_usd", "api_seconds", "acceptance_rate"),
                               ("Known estimated API spend (USD)", "API latency (seconds)", "Accepted / completed episodes")):
        ax.bar(guided_labels, [s[field] or 0 for s in guided])
        ax.tick_params(axis="x", labelsize=8)
        ax.set_ylabel(label)
        for index, summary in enumerate(guided):
            if summary[field] is None:
                ax.text(index, 0, "N/A", ha="center", va="bottom")
    unknown = sum(s["incomplete_accounting_runs"] for s in guided)
    if unknown:
        axes[0].set_title(f"Runs with incomplete cost: {unknown}", fontsize=9)
    save(fig, "api_cost_latency_acceptance")

    fig, ax = plt.subplots(figsize=(7, 4))
    llm = next((s for s in summaries if s["method"] == "openai"), {field: 0 for field in TOKEN_FIELDS})
    ax.bar(("Uncached", "Cache reads", "Cache writes", "Output"),
           [llm["uncached_input_tokens"], llm["cached_input_tokens"],
            llm["short_cache_write_tokens"] + llm["long_cache_write_tokens"], llm["output_tokens"]])
    ax.set_ylabel("OpenAI tokens with normalized usage available")
    save(fig, "prompt_cache")
    outcomes = Counter(r["status"] for r in rows)
    (output / "README.txt").write_text(
        f"{note}\nOutcomes: {dict(outcomes)}\n"
        "Success means the requested BMC bound completed, not an unbounded proof.\n"
        "Pending is excluded from solved/failure denominators. NoProgress is inconclusive.\n"
        "Cost uses embedded Garden accounting; older or running results can use JSONL. Unknown charges are not free.\n"
        "Acceptance counts completed guided episodes, not installed instances.\n"
        "Cactus curves contain each method's own solved population. One trial does not estimate variance.\n"
        "benchmarks.csv preserves model versions, budgets, outcomes, progress and API metrics.\n"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", type=Path, nargs="+")
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    render(args.inputs, args.output_dir)
