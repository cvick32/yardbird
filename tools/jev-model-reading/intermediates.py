#!/usr/bin/env python3
"""Probe explicit intermediate answers, independently or with Jev's own notes."""
from __future__ import annotations

import argparse
from collections import defaultdict
import copy
import hashlib
import http.client
import json
import math
from pathlib import Path
import random
import re
import shutil
import subprocess
import sys
import time

import run

VIEWS = ("native", "native-short", "named", "named-short", "grouped")


def named_tables(model):
    functions = {}
    names = {"Read_Int_Int": ["array", "index"], "Write_Int_Int": ["array", "index", "value"],
             "ConstArr_Int_Int": ["value"]}
    for name, table in model.functions.items():
        arity = len(model.signatures[name][0])
        parameters = names.get(name, [f"arg{i}" for i in range(arity)])
        if len(parameters) != arity:
            raise ValueError(f"Unexpected signature for {name}")
        functions[name] = {
            "parameter_order": parameters,
            "entries": [{"arguments": dict(zip(parameters, args)), "result": value}
                        for args, value in table["entries"].items()],
            "default": table["default"],
        }
    return {"constants": dict(model.constants), "functions": functions}


def grouped_tables(model):
    """Lossless trie of complete argument tuples; no query-specific filtering."""
    tables = named_tables(model)
    functions = {}
    for name, table in tables["functions"].items():
        parameters = table["parameter_order"]
        if not parameters:
            raise ValueError("Grouped function tables require at least one argument")
        entries = {}
        for row in table["entries"]:
            keys = [run.smt(row["arguments"][p]) for p in parameters]
            node = entries
            for key in keys[:-1]:
                node = node.setdefault(key, {})
            if keys[-1] in node:
                raise ValueError("Duplicate grouped argument tuple")
            node[keys[-1]] = row["result"]
        functions[name] = {"default": table["default"], "argument_order": parameters, "entries": entries}
    return {"constants": tables["constants"], "functions": functions}


def rename_domains(value, reverse=False):
    # Exact domain tokens, not substring replacement (val!1 is not val!12).
    pattern = re.compile(r"\barray_(\d+)\b" if reverse else r"\bArray_Int_Int!val!(\d+)\b")
    prefix = "Array_Int_Int!val!" if reverse else "array_"
    if isinstance(value, str):
        return pattern.sub(lambda match: prefix + match[1], value)
    if isinstance(value, dict):
        return {rename_domains(k, reverse): rename_domains(v, reverse) for k, v in value.items()}
    if isinstance(value, list):
        return [rename_domains(v, reverse) for v in value]
    return value


NESTED_EXAMPLE = """This is a synthetic worked example, unrelated to the supplied countermodel. All symbols and values below are local to this example. Read and Write are uninterpreted functions, not real array operations.
src=S!val!2, dst=S!val!0, p=4, q=6.
Write table: (S!val!0,4,1)->S!val!3; default S!val!1.
Read table: (S!val!2,4)->17; (S!val!0,6)->29; (S!val!3,6)->29; (S!val!1,4)->17; default 31.
Evaluate Read(Write(dst,p,Read(src,p)),q):
Read(src,p)=Read(S!val!2,4)=17 by its explicit entry.
Write(dst,p,17)=Write(S!val!0,4,17)=S!val!1 by the default: the entry whose last argument is 1 does not match 17.
Read(S!val!1,q)=Read(S!val!1,6)=31 by the default: the entry with index 4 does not match 6.
Read(dst,q)=Read(S!val!0,6)=29. Since p!=q is true and 31=29 is false, (p!=q) => (Read(Write(dst,p,Read(src,p)),q)=Read(dst,q)) is FALSE.
Now replace the inner source read with constant 1. Write(dst,p,1)=S!val!3 by its explicit entry. Read(S!val!3,6)=29 by its explicit entry. The guard p!=q is still true and 29=29 is true, so this complete instance is TRUE. Neither outcome was inferred from intended array semantics."""


def chains(model):
    # Every interpreted array-domain value is offered, not an oracle shortlist.
    values = list(model.constants.values())
    for table in model.functions.values():
        values.append(table["default"])
        for arguments, value in table["entries"].items():
            values.extend([*arguments, value])
    arrays = sorted({v for v in values if isinstance(v, str) and v.startswith("Array_Int_Int!val!")})
    numbers = ["0", "1", "7", "8", "13"]
    result = {}
    for name, value in [("source-read", "(Read_Int_Int a@0 i@0)"), ("constant-one", "1")]:
        write = f"(Write_Int_Int b@0 i@0 {value})"
        lhs = f"(Read_Int_Int {write} Z@3)"
        rhs = "(Read_Int_Int b@0 Z@3)"
        guard = "(not (= i@0 Z@3))"
        definitions = [("source-value", value, numbers), ("write-result", write, arrays),
                       ("outer-read", lhs, numbers), ("comparison-read", rhs, numbers),
                       ("index-guard", guard, ["true", "false"]),
                       ("equality", f"(= {lhs} {rhs})", ["true", "false"]),
                       ("axiom", f"(=> {guard} (= {lhs} {rhs}))", ["true", "false"])]
        result[name] = [dict(id=f"{name}/{step}", category=step, mode="value",
                             instruction=f"Evaluate this expression in the supplied interpretation: {expression}.",
                             expressions=[expression], labels=labels)
                        for step, expression, labels in definitions]
    return result


def substituted_expression(expression, notes):
    replacements = {run.smt(run.parse(n["expression"])): run.parse(n["selected_value"]) for n in notes}

    def replace(node):
        # Match whole ASTs before descending. Literals and function names are
        # never rewritten, and a replacement is not recursively substituted.
        if isinstance(node, list):
            if run.smt(node) in replacements:
                return replacements[run.smt(node)]
            return [node[0], *(replace(arg) for arg in node[1:])]
        try:
            run.literal(node)
            return node
        except ValueError:
            return replacements.get(node, node)

    return run.smt(replace(run.parse(expression)))


def substitution_chains(model):
    suites = chains(model)
    values = list(model.constants.values())
    for table in model.functions.values():
        values.append(table["default"])
        for args, value in table["entries"].items():
            values.extend([*args, value])
    numbers = [str(n) for n in sorted({v for v in values if type(v) is int})]
    arrays = suites["source-read"][1]["labels"]
    for name, probes in suites.items():
        leaves = [("source-array", "a@0", arrays)] if name == "source-read" else []
        leaves += [("destination-array", "b@0", arrays), ("write-index", "i@0", numbers), ("read-index", "Z@3", numbers)]
        prefix = [dict(id=f"{name}/{step}", category=step, mode="value", expressions=[expr], labels=labels,
                       instruction=f"Evaluate this expression in the supplied interpretation: {expr}.")
                  for step, expr, labels in leaves]
        if name == "constant-one":
            probes = probes[1:]  # A literal already is a value; no API call.
        for p in probes:
            if p["category"] in ("source-value", "outer-read", "comparison-read"):
                p["labels"] = numbers
        suites[name] = prefix + probes
    return suites


def make_request(model, fixture, probe, order, provider_model, source, example, mode, notes, view="native", task_context="procedural"):
    if view not in VIEWS:
        raise ValueError(f"Unknown view {view}")
    if mode == "substituted":
        expression = substituted_expression(probe["expressions"][0], notes)
        probe = dict(probe, expressions=[expression], instruction=f"Evaluate this expression in the supplied interpretation: {expression}.")
    request = run.request_for(model, fixture, probe, "native", order, provider_model,
                              task_context=task_context, vmt_source=source)
    if example != "none":
        request["state"]["worked_examples"] = run.WORKED_EXAMPLES if example == "generic" else NESTED_EXAMPLE
    if mode == "carried":
        request["state"]["previous_answers"] = {
            "meaning": "Your earlier answers in this chain, not checked or corrected by a solver. Use them as working notes; they may be wrong. Re-evaluate them against the interpretation if necessary. The original expression in the question remains authoritative.",
            "answers": copy.deepcopy(notes),
        }
    if view.startswith("named"):
        request["state"]["model"] = named_tables(model)
        request["state"]["model_format"] = "Full interpretation with named argument fields. parameter_order gives positional argument order. A row matches only if ALL its argument values match; otherwise use default. No entries are omitted. Omitted symbols are unknown."
    if view == "grouped":
        request["state"]["model"] = grouped_tables(model)
        request["state"]["model_format"] = "Full interpretation grouped by successive argument values. Each function's argument_order gives the nesting order in entries. Resolve arguments to their model values, then follow one key per argument. Keys are SMT value strings. Only a complete path is an explicit entry. If ANY key is absent, use that function's top-level default; never borrow a result from another branch. All constants, entries, and defaults are retained. Omitted symbols are unknown."
    if view.endswith("-short"):
        request = rename_domains(request)
    return request


def lookup_probes(model):
    """Fixed diagnostic partial evaluations; not a production context strategy."""
    arrays = chains(model)["source-read"][1]["labels"]
    definitions = [
        ("write-nested", "(Write_Int_Int b@0 i@0 (Read_Int_Int a@0 i@0))", arrays),
        ("write-value-resolved", "(Write_Int_Int b@0 i@0 7)", arrays),
        ("write-array-resolved", "(Write_Int_Int Array_Int_Int!val!0 i@0 7)", arrays),
        ("write-fully-resolved", "(Write_Int_Int Array_Int_Int!val!0 0 7)", arrays),
        ("write-control-one", "(Write_Int_Int Array_Int_Int!val!0 0 1)", arrays),
        ("write-control-zero", "(Write_Int_Int Array_Int_Int!val!0 0 0)", arrays),
        ("read-default", "(Read_Int_Int Array_Int_Int!val!1 1)", ["0", "1", "7", "8", "13"]),
        ("read-explicit", "(Read_Int_Int Array_Int_Int!val!6 1)", ["0", "1", "7", "8", "13"]),
    ]
    result = {name: [dict(id=name, category=name, mode="value", expressions=[expression], labels=labels,
                          instruction=f"Evaluate this expression in the supplied interpretation: {expression}.")]
              for name, expression, labels in definitions}
    for value in (7, 1):
        name = f"row-match-{value}"
        # First two arguments are identical. Equality of the third arguments
        # is exactly the full-tuple match predicate; Z3 checks this answer too.
        result[name] = [dict(id=name, category=name, mode="value", expressions=[f"(= {value} 1)"],
                            labels=["true", "false"],
                            instruction=f"The explicit Write_Int_Int row has arguments (Array_Int_Int!val!0, 0, 1) and result Array_Int_Int!val!6. The requested arguments are (Array_Int_Int!val!0, 0, {value}). Does this row match the requested arguments exactly? Answer true only if every argument matches. This asks about this particular row, not whether another row matches.")]
    return result


def grouped_probes(model):
    # Include original nested evaluation, truth controls, and binding questions,
    # so easier lookup improvements cannot hide a failure on the target task.
    probes = lookup_probes(model)
    probes.update({f"diagnostic/{p['id']}": [p] for p in run.suite()})
    return probes


def summarize(path):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    requests = {r["query_id"]: r for r in rows if r["event"] == "request"}
    results = {r["query_id"]: r for r in rows if r["event"] == "result"}
    groups = defaultdict(list)
    for qid, q in requests.items():
        if q["live"]:
            groups[(q.get("view", "native"), q["example"], q["mode"], q["chain"], q["step"])].append(results.get(qid, {"status": "interrupted"}))
    breakdown = []
    for (view, example, mode, chain, step), rs in sorted(groups.items()):
        ps = [r["correct_probability"] for r in rs if r.get("correct_probability") is not None]
        breakdown.append(dict(view=view, example=example, mode=mode, chain=chain, step=step,
                              queries=len(rs), correct=sum(r.get("correct", False) for r in rs),
                              local_correct=sum(r.get("local_correct", r.get("correct", False)) for r in rs),
                              selected_values=[r.get("selected_value") for r in rs],
                              mean_correct_probability=sum(ps) / len(ps) if ps else None))
    costs = [r["cost"]["estimated_usd"] for r in results.values() if r["cost"]["estimated_usd"] is not None]
    live = sum(q["live"] for q in requests.values())
    chains_by_mode = defaultdict(list)
    chain_results = defaultdict(list)
    for qid, q in requests.items():
        if q["live"]:
            chain_results[(q.get("view", "native"), q["example"], q["mode"], q["chain"], q["trial"])].append((q, results.get(qid, {})))
    for (view, example, mode, chain, trial), pairs in chain_results.items():
        final = next((r for q, r in pairs if q["step"] == "axiom"), None)
        if final is not None:
            chains_by_mode[(view, example, mode)].append({"final_correct": final.get("correct", False),
                "all_steps_correct": all(r.get("correct", False) for q, r in pairs), "calls": len(pairs),
                "elapsed_secs": sum(r.get("elapsed_secs", 0) for q, r in pairs)})
    chain_summary = [dict(view=view, example=example, mode=mode, chains=len(cs),
                         final_correct=sum(c["final_correct"] for c in cs),
                         all_steps_correct=sum(c["all_steps_correct"] for c in cs),
                         mean_calls=sum(c["calls"] for c in cs) / len(cs),
                         mean_client_secs=sum(c["elapsed_secs"] for c in cs) / len(cs))
                     for (view, example, mode), cs in sorted(chains_by_mode.items())]
    return dict(requests=len(requests), live_requests=live, results=len(results),
                known_estimated_usd=sum(costs), queries_with_unknown_cost=live - len(costs),
                max_request_bytes=max((q["request_bytes"] for q in requests.values()), default=0),
                client_elapsed_secs=sum(r["elapsed_secs"] for r in results.values()), breakdown=breakdown,
                chain_summary=chain_summary)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--fixture", type=Path, default=run.HERE / "depth3.json")
    parser.add_argument("--suite", choices=["intermediates", "lookup", "substitution", "grouped"], default="intermediates")
    parser.add_argument("--vmt", type=Path, default=run.HERE.parent.parent / "examples/array/array_copy.vmt")
    parser.add_argument("--examples", nargs="+", choices=["none", "generic", "nested"], default=["generic", "nested"])
    parser.add_argument("--modes", nargs="+", choices=["independent", "carried", "substituted"], default=["independent", "carried"])
    parser.add_argument("--task-context", choices=["procedural", "property-directed"], default="procedural")
    parser.add_argument("--views", nargs="+", choices=VIEWS, default=["native"])
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--live", action="store_true")
    parser.add_argument("--model", default="jev-latest")
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument("--max-queries", type=int, default=168)
    parser.add_argument("--env-file", type=Path, default=run.HERE.parent.parent / ".env")
    parser.add_argument("--z3", default=shutil.which("z3"))
    parser.add_argument("--input-usd-per-million", type=float, default=0.042)
    parser.add_argument("--output-usd-per-million", type=float, default=0)
    args = parser.parse_args(argv)
    if args.output.exists():
        parser.error("Output already exists; choose a new file")
    if args.suite in ("lookup", "grouped") and args.modes != ["independent"]:
        parser.error("The lookup and grouped suites require --modes independent")
    if "substituted" in args.modes and args.suite != "substitution":
        parser.error("Substituted mode requires the substitution suite")
    if not args.z3 or args.repeats < 1 or args.max_queries < 1 or not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error("Z3 and positive repeats, timeout, and max queries are required")
    if any(not math.isfinite(r) or r < 0 for r in [args.input_usd_per_million, args.output_usd_per_million]):
        parser.error("Prices must be finite and nonnegative")
    fixture_bytes = args.fixture.read_bytes()
    fixture = json.loads(fixture_bytes)
    source_bytes = args.vmt.read_bytes()
    source = source_bytes.decode("utf-8")
    model = run.NativeModel(fixture)
    suites = {"intermediates": chains, "lookup": lookup_probes, "substitution": substitution_chains, "grouped": grouped_probes}[args.suite](model)
    probes = [p for chain in suites.values() for p in chain]
    keys = {p["id"]: run.answer_key(model, p) for p in probes}
    verification = run.verify_oracle(model, probes, args.z3)
    examples = list(dict.fromkeys(args.examples))
    modes = list(dict.fromkeys(args.modes))
    views = list(dict.fromkeys(args.views))
    count = len(probes) * len(examples) * len(modes) * len(views) * args.repeats
    if count > args.max_queries:
        parser.error(f"Experiment requires {count} queries, exceeding --max-queries")
    # Interleave independent chains but preserve each chain's topological order.
    jobs = [(example, mode, chain, trial, view) for example in examples for mode in modes
            for chain in suites for trial in range(args.repeats) for view in views]
    rng = random.Random(args.seed)
    rng.shuffle(jobs)
    cursors = {job: 0 for job in jobs}
    histories = {job: [] for job in jobs}
    client = run.JevClient(run.api_key(args.env_file), args.timeout) if args.live else None
    failed = False
    try:
        with args.output.open("x") as log:
            def record(row):
                log.write(json.dumps(row, allow_nan=False) + "\n")
                log.flush()

            record(dict(event="experiment", schema_version=1, planned_queries=count,
                        fixture_sha256=hashlib.sha256(fixture_bytes).hexdigest(),
                        vmt_sha256=hashlib.sha256(source_bytes).hexdigest(),
                        runner_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                        shared_runner_sha256=hashlib.sha256(Path(run.__file__).read_bytes()).hexdigest(),
                        verification=verification, provenance=fixture["provenance"],
                        configuration={k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()},
                        offline_note="Dry-run carried requests have empty notes: no oracle answers are substituted."))
            query_id = 0
            while jobs:
                job = rng.choice(jobs)
                example, mode, chain, trial, view = job
                probe = suites[chain][cursors[job]]
                order = list(range(len(probe["labels"])))
                random.Random(f"{args.seed}:{trial}:{probe['id']}").shuffle(order)
                correct_indices, values = keys[probe["id"]]
                correct = [f"o{order.index(i)}" for i in correct_indices]
                actual = substituted_expression(probe["expressions"][0], histories[job]) if mode == "substituted" else probe["expressions"][0]
                request = make_request(model, fixture, probe, order, args.model, source, example, mode, histories[job], view, args.task_context)
                # Scoring only: this result never reaches the request builder.
                local_indices, local_values = (run.answer_key(model, dict(probe, expressions=[actual]))
                                               if mode == "substituted" else (correct_indices, values))
                local_correct = [f"o{order.index(i)}" for i in local_indices]
                query_id += 1
                record(dict(event="request", query_id=query_id, live=args.live, example=example, mode=mode, view=view,
                            chain=chain, trial=trial, step=probe["category"], expression=probe["expressions"][0],
                            evaluated_expression=actual, task_context=args.task_context,
                            local_expected_choices=local_correct, local_oracle_values=local_values,
                            expected_choices=correct, oracle_values=values, request=request,
                            request_bytes=len(json.dumps(request).encode())))
                if client:
                    start = time.monotonic()
                    response = {}
                    try:
                        response = client.decide(request)
                        scored = run.grade(response, correct, request["questions"]["answer"]["criteria"])
                        if scored["status"] == "answered":
                            local_score = run.grade(response, local_correct, request["questions"]["answer"]["criteria"])
                            scored["local_correct"] = local_score["correct"]
                            scored["local_correct_probability"] = local_score["correct_probability"]
                            scored["displayed_value"] = request["state"]["options"][scored["choice"]]
                            selected = probe["labels"][order[int(scored["choice"][1:])]]
                            scored["selected_value"] = selected
                            histories[job].append({"expression": probe["expressions"][0], "selected_value": selected})
                        else:
                            failed = True  # No answer exists to carry forward.
                    except (OSError, ValueError, http.client.HTTPException) as error:
                        scored = {"status": "error", "error": str(error)}
                        failed = True
                    record(dict(event="result", query_id=query_id, response=response,
                                elapsed_secs=time.monotonic() - start, **scored,
                                cost=run.cost(response, args.input_usd_per_million, args.output_usd_per_million)))
                    print(f"{query_id}/{count} {view}/{example}/{mode}/{probe['id']}: {scored.get('selected_value', scored['status'])} correct={scored.get('correct')}", file=sys.stderr)
                    if failed:
                        break
                cursors[job] += 1
                if cursors[job] == len(suites[chain]):
                    jobs.remove(job)
    finally:
        if client:
            client.close()
    print(json.dumps(summarize(args.output), indent=2))
    return int(failed)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1)
