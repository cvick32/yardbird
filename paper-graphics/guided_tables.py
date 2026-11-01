"""Generate paper-ready TeX tables from Garden results or a main_eval manifest.

Embedded api_usage is authoritative. JSONL supplies candidate-validation counts,
never a second copy of the API bill. Missing counters stay missing, not zero.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import statistics

from guided_comparison import GUIDED, LABELS, METHODS, SOLVED, collect, suite_paths, write_csv

TRACE_EVENTS = re.compile(r'"event"\s*:\s*"(candidate_result|attempt_result|transport_error)"')


def supports(inputs: list[Path]) -> bool:
    runs = [run for path in suite_paths(inputs)
            for run in json.loads(path.read_text()).get("metadata", {}).get("planned_runs", [])]
    return bool(runs) and all(run.split("_d", 1)[0] in METHODS for run in runs)


def trace_metrics(path: Path, method: str) -> dict:
    result = {"trace_available": path.is_file(), "trace_partial": False,
              "checked_proposals": None, "validated_proposals": None,
              "api_error_responses": None, "proposal_outcomes": {}}
    if not path.is_file():
        return result
    outcomes = Counter()
    errors = 0
    with path.open() as stream:
        for line in stream:
            if not TRACE_EVENTS.search(line):
                # A truncated final request has no validation evidence to count.
                if line.strip() and not line.endswith("\n"):
                    try:
                        json.loads(line)
                    except json.JSONDecodeError:
                        result["trace_partial"] = True
                continue
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                if line.endswith("\n"):
                    raise
                result["trace_partial"] = True
                continue
            kind = event["event"]
            if kind == "transport_error":
                errors += 1
            elif kind == "candidate_result" or (kind == "attempt_result" and method == "openai"):
                # JEV's synthetic attempt_result summarizes candidate_result;
                # LLM has one attempt_result per proposed instance.
                outcome = event.get("feedback", {}).get("outcome", "unknown")
                outcomes[outcome] += 1
    result.update(checked_proposals=sum(outcomes.values()),
                  validated_proposals=outcomes["violated"], api_error_responses=errors,
                  proposal_outcomes=dict(outcomes))
    return result


def median(values):
    values = list(values)
    return statistics.median(values) if values else None


def known_sum(rows, field):
    values = [r[field] for r in rows if r.get(field) is not None]
    return sum(values) if values else None


def ratio(a, b):
    return a / b if a is not None and b else None


def build_data(inputs: list[Path]) -> dict:
    rows, summaries = collect(inputs)
    indexed = {(r["method"], r["example"]): r for r in rows}
    sources = []
    for path in suite_paths(inputs):
        data_bytes = path.read_bytes()
        suite = json.loads(data_bytes)
        metadata = suite["metadata"]
        sources.append({"path": str(path.resolve()), "sha256": hashlib.sha256(data_bytes).hexdigest(),
                        "git_commit": metadata.get("git_commit"), "timestamp": metadata.get("timestamp")})
        observed = {(r["run_name"], b["example"]): r for b in suite["benchmarks"] for r in b["result"]}
        for run_index, run in enumerate(metadata["planned_runs"]):
            method = run.split("_d", 1)[0]
            for example_index, example in enumerate(metadata["examples"]):
                row = indexed[(method, example)]
                raw = observed.get((run, example), {})
                payload = next(iter(raw.get("result", {"Pending": None}).values()))
                payload = payload if isinstance(payload, dict) else {}
                schemas = payload.get("used_instances")
                row.update(installed_schemas=len(set(schemas)) if isinstance(schemas, list) else None,
                           indexed_assertions=payload.get("total_instantiations_added"),
                           refinement_steps=payload.get("total_refinement_steps"),
                           unsat_core_available=isinstance(payload.get("unsat_core"), dict),
                           source_file=str(path.resolve()), run_name=run,
                           api_evidence_error=(raw.get("api_usage") or {}).get("evidence_error"),
                           token_usage_incomplete_calls=(raw.get("api_usage") or {}).get("token_usage_incomplete_calls"),
                           checked_proposals=None, validated_proposals=None,
                           api_error_responses=None, trace_available=False, trace_partial=False,
                           proposal_outcomes={})
                if method in GUIDED:
                    log = path.with_suffix(".api") / f"{run_index:04}-{example_index:04}.jsonl"
                    if not log.exists():
                        field, key = ("llm", "llm_log") if method == "openai" else ("decision_model", "jev_log")
                        original = raw.get(field, {}).get(key)
                        if original:
                            log = Path(original)
                    row.update(trace_metrics(log, method))
                    if not row["trace_available"] and row["api_evidence_available"] and row["api_calls"] == 0:
                        row.update(checked_proposals=0, validated_proposals=0, api_error_responses=0)
                    row["trace_path"] = str(log.resolve()) if log.exists() else None
                else:
                    row["trace_path"] = None
    solved_sets = [{r["example"] for r in rows if r["method"] == s["method"] and r["status"] in SOLVED}
                   for s in summaries]
    common = set.intersection(*solved_sets) if solved_sets else set()
    for summary in summaries:
        selected = [r for r in rows if r["method"] == summary["method"]]
        completed = [r for r in selected if r["status"] != "Pending"]
        solved = [r for r in completed if r["status"] in SOLVED]
        status_counts = Counter(r["status"] for r in selected)
        summary.update(status_counts=dict(status_counts),
                       solved_percent=100 * summary["solved"] / summary["completed"] if summary["completed"] else None,
                       runtime_sum_seconds=sum(r["runtime_seconds"] for r in completed),
                       solved_runtime_median_seconds=median(r["runtime_seconds"] for r in solved),
                       common_solved=len(common),
                       common_solved_runtime_median_seconds=median(r["runtime_seconds"] for r in selected if r["example"] in common),
                       solved_without_api_calls=sum(r["api_calls"] == 0 and r["api_evidence_available"] for r in solved),
                       installed_schemas_known=known_sum(completed, "installed_schemas"),
                       installed_schema_coverage=sum(r["installed_schemas"] is not None for r in completed),
                       indexed_assertions_known=known_sum(completed, "indexed_assertions"),
                       indexed_assertion_coverage=sum(r["indexed_assertions"] is not None for r in completed),
                       solved_installed_schemas=known_sum(solved, "installed_schemas"),
                       solved_schema_coverage=sum(r["installed_schemas"] is not None for r in solved),
                       solved_schema_median=median(r["installed_schemas"] for r in solved if r["installed_schemas"] is not None),
                       refinement_steps_known=known_sum(completed, "refinement_steps"),
                       refinement_coverage=sum(r["refinement_steps"] is not None for r in completed),
                       unsat_core_runs=sum(r["unsat_core_available"] for r in completed),
                       checked_proposals=known_sum(completed, "checked_proposals"),
                       validated_proposals=known_sum(completed, "validated_proposals"),
                       trace_coverage=sum(r["trace_available"] and (r["api_calls"] > 0 or not r["api_evidence_available"]) for r in completed),
                       trace_required_runs=sum(r["api_calls"] > 0 or not r["api_evidence_available"] for r in completed),
                       missing_validation_logs=sum(r["checked_proposals"] is None for r in completed) if summary["method"] in GUIDED else 0,
                       partial_traces=sum(r["trace_partial"] for r in completed),
                       api_error_responses=known_sum(completed, "api_error_responses"),
                       api_evidence_errors=sum(bool(r["api_evidence_error"]) for r in completed),
                       token_usage_incomplete_calls=known_sum(completed, "token_usage_incomplete_calls"),
                       resolved_models=sorted({m for r in selected for m in (r["resolved_models"] or "").split(";") if m}),
                       target_depths=sorted({r["target_depth"] for r in completed if r["target_depth"] is not None}),
                       strict_guidance=all(r["no_guided_fallback"] is True for r in completed) if summary["method"] in GUIDED else None)
        summary["proposal_outcomes"] = dict(sum((Counter(r["proposal_outcomes"]) for r in completed), Counter()))
        summary["validation_percent"] = 100 * ratio(summary["validated_proposals"], summary["checked_proposals"]) if summary["checked_proposals"] else None
        summary["known_usd_per_solved"] = ratio(summary["estimated_subtotal_usd"], summary["solved"])
        summary["known_usd_per_validated_proposal"] = ratio(summary["estimated_subtotal_usd"], summary["validated_proposals"])
        summary["calls_per_validated_proposal"] = ratio(summary["api_calls"], summary["validated_proposals"])
        summary["cache_read_percent"] = 100 * ratio(summary["cached_input_tokens"], summary["input_tokens"]) if summary["input_tokens"] else None
    return {"schema_version": 1, "sources": sources, "common_solved_examples": sorted(common),
            "summaries": summaries, "benchmarks": rows}


def tex_escape(value: object) -> str:
    escapes = {"\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$", "#": r"\#",
               "_": r"\_", "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}", "^": r"\textasciicircum{}"}
    return "".join(escapes.get(c, c) for c in str(value))


def number(value, digits=0):
    return "--" if value is None else f"{value:,.{digits}f}"


def bounded(value, incomplete, digits=0):
    return number(value, digits) + ("*" if incomplete and value is not None else "")


def table_specs(data: dict) -> list[dict]:
    summaries = data["summaries"]
    guided = [s for s in summaries if s["method"] in GUIDED]
    short = {"jev": "JEV", "jev-fallback": "JEV + YB", "openai": "Astra", "yardbird": "Yardbird", "z3": "Z3"}
    labels = [short[s["method"]] for s in summaries]
    def incomplete(s):
        return bool(s["unknown_cost_calls"] or s["missing_api_evidence"] or s["api_evidence_errors"])
    def cost(s):
        if s["method"] in GUIDED and s["missing_api_evidence"] == s["planned"]:
            return "--"
        return bounded(s["estimated_subtotal_usd"], incomplete(s), 2)
    outcomes = {
        "name": "evaluation_summary", "caption": "Verification outcomes and API expenditure.",
        "headers": ["Method", "Solved", "Timeout", "Stalled", "Other", "Median (s)", "API calls", "API USD"],
        "rows": [[short[s["method"]], f'{s["solved"]}/{s["planned"]}', s["status_counts"].get("Timeout", 0),
                  s["status_counts"].get("NoProgress", 0),
                  sum(n for status, n in s["status_counts"].items() if status not in SOLVED | {"Timeout", "NoProgress"}),
                  number(s["solved_runtime_median_seconds"], 3), number(s["api_calls"]), cost(s)] for s in summaries],
        "notes": "Solved means Success or FoundProof; completion of a BMC bound is not an unbounded proof. "
                 "Stalled means NoProgress; Other includes errors and pending results. Medians use each method's own solved population. "
                 "API USD is the known usage-based estimate across all outcomes; * marks incomplete accounting, not free calls. AWS compute is excluded.",
    }
    runtime_metrics = [
        ("Target BMC depths", lambda s: ", ".join(map(str, s["target_depths"])) or "--"),
        ("Guidance fallback disabled", lambda s: "--" if s["strict_guidance"] is None else str(s["strict_guidance"])),
        ("Planned benchmarks", lambda s: number(s["planned"])),
        ("Completed benchmark attempts", lambda s: number(s["completed"])),
        ("Solved (%) of completed", lambda s: number(s["solved_percent"], 1)),
        ("Pending benchmarks", lambda s: number(s["status_counts"].get("Pending", 0))),
        ("Sum of benchmark runtimes (s)", lambda s: number(s["runtime_sum_seconds"], 1)),
        ("Median runtime, own solves (s)", lambda s: number(s["solved_runtime_median_seconds"], 3)),
        ("Common solved benchmarks", lambda s: number(s["common_solved"])),
        ("Median runtime, common solves (s)", lambda s: number(s["common_solved_runtime_median_seconds"], 3)),
        ("Solved without API calls", lambda s: number(s["solved_without_api_calls"])),
    ]
    runtime = {"name": "runtime_details", "caption": "Runtime populations and coverage.",
               "headers": ["Metric", *labels], "rows": [[label, *(fn(s) for s in summaries)] for label, fn in runtime_metrics],
               "notes": "Common solves are the intersection of solved benchmark sets across all displayed methods. "
                        "Runtime sums include timeouts and are not AWS wall-clock duration. One trial per method/benchmark; no variance estimate."}
    inst_metrics = [
        ("Installed schemas, known total", lambda s: bounded(s["installed_schemas_known"], s["installed_schema_coverage"] < s["completed"])),
        ("Schema-count coverage (runs)", lambda s: f'{s["installed_schema_coverage"]}/{s["completed"]}'),
        ("Indexed assertions, known total", lambda s: bounded(s["indexed_assertions_known"], s["indexed_assertion_coverage"] < s["completed"])),
        ("Assertion-count coverage (runs)", lambda s: f'{s["indexed_assertion_coverage"]}/{s["completed"]}'),
        ("Installed schemas on solved runs", lambda s: bounded(s["solved_installed_schemas"], s["solved_schema_coverage"] < s["solved"])),
        ("Median schemas on solved runs", lambda s: number(s["solved_schema_median"], 1)),
        ("Driver loop iterations, known total", lambda s: bounded(s["refinement_steps_known"], s["refinement_coverage"] < s["completed"])),
        ("Runs with saved unsat cores", lambda s: number(s["unsat_core_runs"])),
    ]
    inst = {"name": "instantiation_stats", "caption": "Installed instantiations and available solver evidence.",
            "headers": ["Metric", *labels], "rows": [[label, *(fn(s) for s in summaries)] for label, fn in inst_metrics],
            "notes": "A schema is a distinct normalized term in used_instances, counted separately per benchmark. "
                     "Indexed assertions use total_instantiations_added; one schema may be asserted at many frames. "
                     "* marks a subtotal over runs with saved counters: missing timeout counters are not zeros. "
                     "Counts describe Yardbird-installed instances, not internal Z3 array-theory lemmas. "
                     "Loop iterations use total_refinement_steps, which includes the initial check at each depth, even for Z3. "
                     "Missing unsat cores do not imply zero core utilization."}
    api_metrics = [
        ("Known estimated API spend (USD)", cost),
        ("API calls (incl. unresolved)", lambda s: number(s["api_calls"])),
        ("Calls with unknown cost", lambda s: number(s["unknown_cost_calls"])),
        ("Runs missing API evidence", lambda s: number(s["missing_api_evidence"])),
        ("Runs with accounting errors", lambda s: number(s["api_evidence_errors"])),
        ("API transport errors (recorded)", lambda s: number(s["api_error_responses"])),
        ("Calls with incomplete token usage", lambda s: number(s["token_usage_incomplete_calls"])),
        ("Recorded API latency (s)", lambda s: number(s["api_seconds"], 1)),
        ("Completed guidance episodes", lambda s: number(s["episodes"])),
        ("Successful guidance episodes", lambda s: number(s["accepted_episodes"])),
        ("Fallback guidance episodes", lambda s: number(s["fallback_episodes"])),
        ("Successful episodes (%)", lambda s: number(100*s["acceptance_rate"] if s["acceptance_rate"] is not None else None, 1)),
        ("Proposals checked (recorded)", lambda s: bounded(s["checked_proposals"], s["missing_validation_logs"] or s["partial_traces"])),
        ("Validated proposals (recorded)", lambda s: bounded(s["validated_proposals"], s["missing_validation_logs"] or s["partial_traces"])),
        ("Validated / checked (%)", lambda s: number(s["validation_percent"], 1)),
        ("Proposals true in current model", lambda s: number(s["proposal_outcomes"].get("instance_true", 0)) if s["checked_proposals"] is not None else "--"),
        ("Proposals already present", lambda s: number(s["proposal_outcomes"].get("already_present", 0)) if s["checked_proposals"] is not None else "--"),
        ("Proposals undetermined", lambda s: number(s["proposal_outcomes"].get("undetermined", 0)) if s["checked_proposals"] is not None else "--"),
        ("Validation-log coverage (API runs)", lambda s: f'{s["trace_coverage"]}/{s["trace_required_runs"]}'),
        ("Input tokens (reported)", lambda s: number(s["input_tokens"])),
        ("Cached input tokens (reported)", lambda s: number(s["cached_input_tokens"])),
        ("Cache-read share of input (%)", lambda s: number(s["cache_read_percent"], 1)),
        ("Cache-write tokens (reported)", lambda s: number(s["short_cache_write_tokens"]+s["long_cache_write_tokens"])),
        ("Output tokens (reported)", lambda s: number(s["output_tokens"])),
        ("Known spend / solved benchmark (USD)", lambda s: bounded(s["known_usd_per_solved"], incomplete(s), 3)),
        ("Known spend / validated proposal (USD)", lambda s: bounded(s["known_usd_per_validated_proposal"], incomplete(s), 5)),
        ("API calls / validated proposal", lambda s: number(s["calls_per_validated_proposal"], 2)),
    ]
    api = {"name": "api_usage", "caption": "API expenditure, validation yield, and token usage.",
           "headers": ["Metric", *(LABELS[s["method"]] for s in guided)],
           "rows": [[label, *(fn(s) for s in guided)] for label, fn in api_metrics],
           "notes": "A validated proposal evaluates false in the current abstract model and passes local checks; "
                    "it is not a solved benchmark or proof of installation. JEV can accept several proposals per episode; "
                    "the LLM proposes one. Counts include observed work on unsuccessful runs; traces interrupted at timeout can be incomplete. "
                    "Ratios of recorded proposals exclude unseen proposals; spend per solve includes costs of failed runs. "
                    "* marks incomplete cost or validation evidence. Zero-call runs need no validation log. Token and latency totals include only reported usage. "
                    "Resolved models: " + "; ".join(f'{LABELS[s["method"]]}: {", ".join(s["resolved_models"]) or "unknown"}' for s in guided) + "."}
    return [outcomes, runtime, inst, *([api] if guided else [])]


def render_tex(spec: dict) -> str:
    columns = "l" + "r" * (len(spec["headers"])-1)
    def row(cells):
        return " & ".join(tex_escape(c) for c in cells) + r" \\"
    return "\n".join([
        "% Generated by guided_tables.py; requires booktabs. Use in a full-width table* for two-column papers.",
        r"\begin{table*}[t]", r"\centering", r"\small", r"\setlength{\tabcolsep}{4pt}",
        r"\caption{"+tex_escape(spec["caption"])+"}", r"\label{tab:"+spec["name"].replace("_", "-")+"}",
        r"\begin{tabular}{"+columns+"}", r"\toprule", row(spec["headers"]), r"\midrule",
        *(row(cells) for cells in spec["rows"]), r"\bottomrule", r"\end{tabular}",
        r"\par\smallskip", r"\begin{minipage}{\textwidth}\footnotesize",
        tex_escape(spec["notes"]), r"\end{minipage}", r"\end{table*}", "",
    ])


def generate(inputs: list[Path], output: Path) -> dict:
    data = build_data(inputs)
    specs = table_specs(data)
    output.mkdir(parents=True, exist_ok=True)
    paths = []
    for spec in specs:
        path = output / (spec["name"] + ".tex")
        path.write_text(render_tex(spec))
        paths.append(path)
    (output / "table_data.json").write_text(json.dumps(data, indent=2, allow_nan=False)+"\n")
    def csv_rows(rows):
        return [{k: json.dumps(v, sort_keys=True) if isinstance(v, (dict, list)) else v
                 for k, v in row.items()} for row in rows]
    write_csv(output / "summary.csv", csv_rows(data["summaries"]))
    write_csv(output / "benchmarks.csv", csv_rows(data["benchmarks"]))
    (output / "README.txt").write_text(
        "Generated from Garden results; see table_data.json for source hashes and exact values.\n"
        "Include individual TeX fragments with booktabs loaded; they use full-width table* environments.\n"
        "The four fragments separate outcomes, runtime populations, installed instances, and API work.\n"
        "Preview: pdflatex -interaction=nonstopmode -halt-on-error preview.tex (from this directory).\n"
        "API costs are estimates at the run's configured rates, not invoices; AWS compute is excluded.\n"
        "An asterisk marks incomplete totals. Missing installation counters are never filled with zero.\n"
        "Successful guidance episodes, validated proposals, installed schemas, and assertions are distinct.\n"
        "No new solver or model calls are made.\n")
    (output / "preview.tex").write_text("\n".join([
        r"\documentclass[10pt]{article}", r"\usepackage[margin=0.7in]{geometry}",
        r"\usepackage{booktabs}", r"\begin{document}",
        *(r"\input{"+p.name+"}\n\\clearpage" for p in paths), r"\end{document}", "",
    ]))
    return {"tex_paths": paths, "specs": specs, "data": data}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", nargs="+", type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args()
    generated = generate(args.inputs, args.output_dir)
    for path in generated["tex_paths"]:
        print(path)


if __name__ == "__main__":
    main()
