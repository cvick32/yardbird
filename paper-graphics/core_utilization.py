"""Replay saved array instantiations at a final BMC depth and measure fresh cores.

No inference calls or refinement search. Supports the quantifier-free Int-array
VMT corpus and full-unroll installation used by main_eval. Other encodings fail
explicitly rather than silently reconstructing a different verification problem.
"""

from __future__ import annotations

import argparse
import csv
import fnmatch
import hashlib
import json
import re
import subprocess
import time
from collections import Counter, defaultdict
from pathlib import Path

import z3

TOKEN = re.compile(r';[^\n]*|\|[^|]*\||"(?:""|[^"])*"|[()]|[^\s()]+')
OFFSET = re.compile(r"^(.*)\+(\d+)$")
PRELUDE = """(declare-sort Array_Int_Int 0)
(declare-fun Read_Int_Int (Array_Int_Int Int) Int)
(declare-fun Write_Int_Int (Array_Int_Int Int Int) Array_Int_Int)
(declare-fun ConstArr_Int_Int (Int) Array_Int_Int)
"""


def parse(text):
    stack, roots = [], []
    for token in TOKEN.findall(text):
        if token.startswith(";"):
            continue
        if token == "(":
            node = []
            (stack[-1] if stack else roots).append(node)
            stack.append(node)
        elif token == ")":
            if not stack:
                raise ValueError("Unbalanced parentheses")
            stack.pop()
        else:
            (stack[-1] if stack else roots).append(token)
    if stack:
        raise ValueError("Unbalanced parentheses")
    return roots


def render(node):
    return "(" + " ".join(map(render, node)) + ")" if isinstance(node, list) else node


def abstract(node):
    if not isinstance(node, list):
        return {"select": "Read_Int_Int", "store": "Write_Int_Int"}.get(node, node)
    if node == ["Array", "Int", "Int"]:
        return "Array_Int_Int"
    if node and node[0] == "Array":
        raise ValueError("Only (Array Int Int) is supported")
    if node and node[0] in ["forall", "exists", "lambda"]:
        raise ValueError(
            "Quantified source/schema requires Yardbird lowering, not this replay"
        )
    if node and node[0] == "!":
        return abstract(node[1])
    if node and node[0] == ["as", "const", ["Array", "Int", "Int"]]:
        return ["ConstArr_Int_Int", abstract(node[1])]
    return [abstract(item) for item in node]


def atoms(node):
    if isinstance(node, list):
        for item in node:
            yield from atoms(item)
    else:
        yield node


class Problem:
    def __init__(self, source):
        commands = parse(source)
        declarations, next_to_current = {}, {}
        formulas = {"init": [], "trans": [], "invar-property": []}
        for command in commands:
            kind = command[0]
            if kind not in {
                "declare-fun",
                "define-fun",
                "set-logic",
                "set-info",
                "set-option",
            }:
                raise ValueError(f"Unsupported VMT command: {kind}")
            if kind == "declare-fun":
                if command[2]:
                    raise ValueError(
                        "Non-nullary source declarations are not supported"
                    )
                declarations[command[1]] = abstract(command[3])
            if (
                kind == "define-fun"
                and isinstance(command[4], list)
                and command[4][0] == "!"
            ):
                term = command[4]
                attributes = dict(zip(term[2::2], term[3::2]))
                if ":next" in attributes:
                    if not isinstance(term[1], str):
                        raise ValueError("Non-symbol :next alias")
                    next_to_current[attributes[":next"]] = term[1]
                for key in formulas:
                    if ":" + key in attributes:
                        if command[2]:
                            raise ValueError("Parameterized VMT metadata formula")
                        formulas[key].append(command[1])
                unknown = set(attributes) - {
                    ":next",
                    ":init",
                    ":trans",
                    ":invar-property",
                }
                if unknown:
                    raise ValueError(f"Unsupported VMT annotation: {unknown}")
        if not all(formulas.values()):
            raise ValueError("Missing init, transition, or property formula")
        self.variables = {
            n: s for n, s in declarations.items() if n not in next_to_current
        }
        self.next_to_current = next_to_current
        self.declarations = dict(declarations)
        extras = []
        for nxt, cur in next_to_current.items():
            if nxt not in declarations:
                extras.append(f"(declare-fun {nxt} () {self.variables[cur]})")
                self.declarations[nxt] = self.variables[cur]
        # Define-fun bodies are expanded by Z3 before frame substitution.
        transformed = [
            render(abstract(c))
            for c in commands
            if c[0] in {"declare-fun", "define-fun"}
        ]
        self.base = PRELUDE + "\n".join(extras + transformed)
        assertions = ["(assert (and " + " ".join(formulas[k]) + "))" for k in formulas]
        self.init, self.trans, self.prop = z3.parse_smt2_string(
            self.base + "\n" + "\n".join(assertions)
        )
        self.sorts = {
            "Int": z3.IntSort(),
            "Bool": z3.BoolSort(),
            "Real": z3.RealSort(),
            "Array_Int_Int": z3.DeclareSort("Array_Int_Int"),
        }
        for sort in self.variables.values():
            if not isinstance(sort, str) or sort not in self.sorts:
                raise ValueError(f"Unsupported sort {sort}")

    def var(self, name, frame=None):
        symbol = name.strip("|") + (f"@{frame}" if frame is not None else "")
        return z3.Const(symbol, self.sorts[self.declarations[name]])

    def ground(self, term, frame):
        replacements = [(self.var(n), self.var(n, frame)) for n in self.variables]
        replacements += [
            (self.var(n), self.var(cur, frame + 1))
            for n, cur in self.next_to_current.items()
        ]
        return z3.substitute(term, replacements)

    def placements(self, schema, depth):
        nodes = parse(schema)
        if len(nodes) != 1:
            raise ValueError("Expected one schema formula")
        abstract(nodes[0])  # Reject unsupported quantified schemas.
        offsets = {a: OFFSET.fullmatch(a) for a in sorted(set(atoms(nodes[0])))}
        offsets = {a: m for a, m in offsets.items() if m}
        width = max((int(m[2]) for m in offsets.values()), default=0)
        if offsets and min(int(m[2]) for m in offsets.values()) != 0:
            raise ValueError("Schema is not normalized to offset zero")
        for match in offsets.values():
            if match[1] not in self.variables:
                raise ValueError(f"Unknown schema variable {match[1]}")
        decls = [
            f"(declare-fun {a} () {self.variables[m[1]]})" for a, m in offsets.items()
        ]
        (term,) = z3.parse_smt2_string(
            self.base + "\n" + "\n".join(decls) + f"\n(assert {schema})"
        )
        for end in range(width, depth + 1):
            replacements = [(self.var(n), self.var(n, end)) for n in self.variables]
            replacements += [
                (
                    z3.Const(a, self.sorts[self.variables[m[1]]]),
                    self.var(m[1], end - width + int(m[2])),
                )
                for a, m in offsets.items()
            ]
            yield end, z3.substitute(term, replacements)


def replay(source, schemas, depth, timeout_ms=10000, save_query=None):
    problem = Problem(source)
    schemas = list(dict.fromkeys(schemas))
    solver = z3.SolverFor("UFLIA")
    solver.set(timeout=timeout_ms, random_seed=0)
    solver.add(problem.ground(problem.init, 0))
    solver.add([problem.ground(problem.trans, t) for t in range(depth)])
    solver.add(z3.Not(problem.ground(problem.prop, depth)))
    labels, seen = {}, set()
    for index, schema in enumerate(schemas):
        for end, formula in problem.placements(schema, depth):
            key = formula.sexpr()
            if key in seen:
                continue
            seen.add(key)
            label = f"replay_inst_{index}_{end}"
            labels[label] = {"schema_index": index, "end_frame": end, "formula": key}
            solver.assert_and_track(formula, label)
    if save_query:
        save_query.parent.mkdir(parents=True, exist_ok=True)
        save_query.write_text(
            "(set-option :produce-unsat-cores true)\n"
            + solver.sexpr()
            + "\n(check-sat-assuming ("
            + " ".join(labels)
            + "))\n(get-unsat-core)\n"
        )
        save_query.with_suffix(".labels.json").write_text(
            json.dumps({"schemas": schemas, "labels": labels}, indent=2)
        )
    start = time.monotonic()
    result = solver.check()
    elapsed = time.monotonic() - start
    core = [str(x) for x in solver.unsat_core()] if result == z3.unsat else None
    used = (
        sorted({labels[label]["schema_index"] for label in core})
        if core is not None
        else None
    )
    return dict(
        replay_status=str(result),
        reason=solver.reason_unknown() if result == z3.unknown else None,
        replay_seconds=elapsed,
        solver_timeout_ms=timeout_ms,
        replay_depth=depth,
        installed_schemas=len(schemas),
        replayed_assertions=len(labels),
        core_schemas=len(used) if used is not None else None,
        core_assertions=len(core) if core is not None else None,
        schema_utilization_percent=100 * len(used) / len(schemas)
        if used is not None and schemas
        else None,
        assertion_utilization_percent=100 * len(core) / len(labels)
        if core is not None and labels
        else None,
        core_schema_indices=used,
        core_labels=core,
    )


def load_rows(inputs):
    paths = []
    for path in inputs:
        paths.extend(
            sorted((path / "raw").glob("*/*.json")) if path.is_dir() else [path]
        )
    if not paths:
        raise ValueError("No Garden result JSON found")
    for path in dict.fromkeys(p.resolve() for p in paths):
        data = json.loads(path.read_text())
        revision = data.get("metadata", {}).get("git_commit")
        for benchmark in data["benchmarks"]:
            for trial, raw in enumerate(benchmark["result"]):
                status, payload = next(iter(raw["result"].items()))
                yield path, revision, benchmark["example"], trial, raw, status, payload


def write_reports(output, rows, excluded=None):
    output.mkdir(parents=True, exist_ok=True)
    (output / "results.json").write_text(
        json.dumps(
            {
                "core_kind": "post_hoc_final_depth_replay",
                "z3_version": z3.get_version_string(),
                "original_outcome_filter": "Success",
                "excluded_original_outcomes": excluded or {},
                "benchmarks": rows,
            },
            indent=2,
        )
    )
    scalar = [{k: v for k, v in r.items() if not isinstance(v, list)} for r in rows]
    with (output / "benchmarks.csv").open("w", newline="") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=list(dict.fromkeys(k for r in scalar for k in r))
            or ["method", "run_name", "example", "historical_status", "replay_status"],
        )
        writer.writeheader()
        writer.writerows(scalar)
    groups = defaultdict(list)
    for row in rows:
        groups[(row["run_name"], row["replay_depth"])].append(row)
    summaries = []
    lines = [
        "# Post-hoc core utilization",
        "",
        "Only originally successful strategy/benchmark runs are replayed.",
        "",
        "| Configuration | Frame | UNSAT / replays | Schemas in core / installed | Schema utilization | Assertion utilization |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for (run, depth), group in groups.items():
        covered = [r for r in group if r["replay_status"] == "unsat"]
        count = sum(r["installed_schemas"] for r in covered)
        core = sum(r["core_schemas"] for r in covered)
        assertions = sum(r["replayed_assertions"] for r in covered)
        core_assertions = sum(r["core_assertions"] for r in covered)
        summary = dict(
            run_name=run,
            replay_depth=depth,
            runs=len(group),
            unsat_replays=len(covered),
            installed_schemas=count if covered else None,
            core_schemas=core if covered else None,
            schema_utilization_percent=100 * core / count if count else None,
            replayed_assertions=assertions if covered else None,
            core_assertions=core_assertions if covered else None,
            assertion_utilization_percent=100 * core_assertions / assertions
            if assertions
            else None,
        )
        summaries.append(summary)
        pct = f"{100 * core / count:.1f}%" if count else "N/A"
        assertion_pct = (
            f"{100 * core_assertions / assertions:.1f}%" if assertions else "N/A"
        )
        lines.append(
            f"| {run} | {depth} | {len(covered)}/{len(group)} | {core}/{count} | {pct} | {assertion_pct} |"
        )
    (output / "summary.json").write_text(json.dumps(summaries, indent=2))
    lines += [
        "",
        "Fresh cores from one final-depth query with saved schemas replayed across eligible frames. "
        "No model calls or refinement search. UNSAT cores need not be minimal. SAT, unknown, missing "
        "schemas, and unsupported encodings have no utilization percentage. Pooled percentages use "
        "only UNSAT replays; compare common benchmarks at the same bound.",
    ]
    if excluded:
        lines += ["", "Excluded original outcomes (not replayed):", ""]
        for run, counts in excluded.items():
            lines.append(
                f"- {run}: "
                + ", ".join(
                    f"{status}={count}" for status, count in sorted(counts.items())
                )
            )
    (output / "report.md").write_text("\n".join(lines) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", nargs="+", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument(
        "--repo", type=Path, default=Path(__file__).resolve().parents[1]
    )
    parser.add_argument("--methods", nargs="+", default=["openai", "jev", "yardbird"])
    parser.add_argument(
        "--examples", nargs="+", default=["*"], help="Filename glob patterns"
    )
    parser.add_argument(
        "--depth",
        type=int,
        help="Zero-based final frame; default is saved target depth minus one",
    )
    parser.add_argument("--timeout-seconds", type=float, default=10)
    parser.add_argument("--save-queries", action="store_true")
    args = parser.parse_args()
    if args.timeout_seconds <= 0 or (args.depth is not None and args.depth < 0):
        parser.error("Timeout must be positive and depth must be nonnegative")
    rows = []
    excluded = defaultdict(Counter)
    for path, revision, example, trial, raw, status, payload in load_rows(args.inputs):
        method = raw["run_name"].split("_d", 1)[0]
        if method not in args.methods or not any(
            fnmatch.fnmatch(Path(example).name, p) for p in args.examples
        ):
            continue
        if status != "Success":
            excluded[raw["run_name"]][status] += 1
            continue
        depth = args.depth if args.depth is not None else raw["depth"] - 1
        row = dict(
            method=method,
            run_name=raw["run_name"],
            example=example,
            trial=trial,
            source_file=str(path),
            revision=revision,
            historical_status=status,
            replay_depth=depth,
            replay_status="missing_schemas",
        )
        schemas = payload.get("used_instances") if isinstance(payload, dict) else None
        if schemas is not None:
            try:
                if (
                    raw.get("strategy") != "abstract"
                    or raw.get("instantiation_strategy") != "full-unroll"
                ):
                    raise ValueError("Replay supports abstract/full-unroll runs only")
                if any(
                    raw.get(k)
                    for k in [
                        "preprocess_exact_read_after_write",
                        "abstract_recurrent_products",
                        "guarded_read_updates",
                    ]
                ):
                    raise ValueError("Transformed encoding is not supported")
                if (raw.get("auxiliary_synthesis") or {}).get(
                    "trigger", "off"
                ) != "off":
                    raise ValueError("Auxiliary synthesis is not supported")
                if not isinstance(revision, str) or not re.fullmatch(
                    "[0-9a-fA-F]{7,40}", revision
                ):
                    raise ValueError(
                        "Missing saved git revision for source reconstruction"
                    )
                source = subprocess.check_output(
                    ["git", "show", f"{revision}:{example}"],
                    cwd=args.repo,
                    text=True,
                    stderr=subprocess.PIPE,
                )
                row["source_sha256"] = hashlib.sha256(source.encode()).hexdigest()
                key = hashlib.sha256(
                    f"{path}:{example}:{raw['run_name']}:{trial}".encode()
                ).hexdigest()[:12]
                query = (
                    args.output
                    / "queries"
                    / f"{method}-{Path(example).stem}-{key}.smt2"
                    if args.save_queries
                    else None
                )
                row.update(
                    replay(
                        source, schemas, depth, int(args.timeout_seconds * 1000), query
                    )
                )
                row["historical_assertions"] = payload.get("total_instantiations_added")
            except (ValueError, z3.Z3Exception, subprocess.CalledProcessError) as error:
                row.update(replay_status="unsupported_or_error", reason=str(error))
        rows.append(row)
        write_reports(args.output, rows, excluded)
        print(
            f"{method}: {Path(example).name}: {row['replay_status']}; schema utilization={row.get('schema_utilization_percent')}",
            flush=True,
        )
    write_reports(args.output, rows, excluded)
    print(f"Saved {args.output / 'report.md'} ({len(rows)} successful original runs).")


if __name__ == "__main__":
    main()
