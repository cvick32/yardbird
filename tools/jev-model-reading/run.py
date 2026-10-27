#!/usr/bin/env python3
"""Controlled Jev model-reading probes; offline by default, standard library only."""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import http.client
import json
import math
import os
from pathlib import Path
import random
import re
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
PROPERTY_DIRECTED_PROMPT = (HERE.parent.parent / "src/policy/decision_model/prompts/property-directed.txt").read_text().strip()
ATOM = re.compile(r"[A-Za-z_][A-Za-z0-9_@!+.-]*\Z")
PROCEDURAL_PROMPT = """You are evaluating an abstract countermodel while verifying the supplied VMT program. Its Read/Write functions are uninterpreted; intended array axioms need not hold in this interpretation. Do not simplify an expression using an array axiom.
Treat the interpretation as an executable lookup table:
1. Evaluate applications from the innermost expression outward. Resolve every named argument to its model value before looking up the application. Distinct expressions may denote the same model value.
2. An explicit function entry matches only if EVERY argument value matches the corresponding argument in that entry. If no complete tuple matches, use that function's default. A default is not an unknown value. An unmodeled symbol is unknown; do not invent its value.
3. Evaluate equalities and Boolean connectives after evaluating their operands. An implication is FALSE exactly when its antecedent is true and its consequent is false. A false antecedent makes the implication true.
4. Follow the specific question. For value or truth questions, report the actual value, including true controls. For instantiation selection, choose an option whose COMPLETE instantiated formula is false. Unknown is not false. For a partial binding, coordinate the remaining bindings to admit a false completion while preserving fixed bindings.
Use only the offered answers. If multiple options satisfy the question, any is acceptable. The original VMT explains the problem but does not override the supplied interpretation."""
WORKED_EXAMPLES = """These are two independent synthetic examples, unrelated to the supplied countermodel. Their symbols and values apply only inside the examples.
Example 1: u=4, v=4. F has entry (4)->9 and default 6. G has entry (9,4)->12 and default 3. Evaluate G(F(u),v): F(u)=F(4)=9; G(9,4)=12 by an exact tuple match. Thus G(F(u),v)=12 is true. In contrast G(F(u),5)=G(9,5)=3 by the default, so G(F(u),5)=12 is false. Matching just the first argument is insufficient.
Example 2: p=2, q=2. H has entry (2)->7 and default 0. The formula (p != q) => (H(p)=0) is true: the antecedent is false, even though the consequent is false. The formula (p=q) => (H(p)=0) is false: its antecedent is true and its consequent is false."""
ABLATIONS = ("property-directed", "procedural", "procedural-examples", "procedural-aliases")
BINDING_ABLATIONS = ("property-directed", "property-directed-term-values")
FALSIFICATION_PROMPT = """You are selecting a refinement for an abstract countermodel. Judge each option by its effect in the supplied interpretation, not by whether it looks like a conventional array operation.
The array axioms describe intended semantics; they are not facts already satisfied by these function tables. Do not use an array axiom to simplify the expression you are evaluating.
For each complete substitution, evaluate the entire instantiated formula using the supplied function entries and defaults. Always prefer substitutions whose formula is **false**. A true instance cannot eliminate this countermodel. An unknown evaluation is not evidence of a violation.
For a partial substitution, prefer bindings that admit a completion making the entire formula false. Coordinate the remaining bindings; a locally plausible choice is insufficient.
Multiple options may yield violations. Select a violating option rather than a nonviolating one."""
REFINEMENT_CONTEXT = (
    "You are helping Yardbird refine an abstraction while verifying an array program. "
    "The solver has returned a candidate counterexample to the program property. "
    "Array operations were replaced by uninterpreted functions, so this interpretation may violate array theory. "
    "Our goal is to find a substitution into an array axiom whose COMPLETE instantiated formula is FALSE in this interpretation. "
    "Asserting that instance then excludes the current abstract counterexample. "
    "An array axiom is valid for real arrays, but its instance is not necessarily true for these abstract function tables. "
    "A true instance does not exclude this counterexample. "
    "Answer the specific question using the supplied interpretation; do not repair the tables or assume array laws already hold. "
    "Some questions are controls with true formulas: do not answer false merely because we seek violations. "
)


def parse(text):
    tokens = re.findall(r"\(|\)|[^\s()]+", text)
    position = 0

    def term():
        nonlocal position
        if position >= len(tokens):
            raise ValueError("Incomplete SMT expression")
        token = tokens[position]
        position += 1
        if token == "(":
            result = []
            while position < len(tokens) and tokens[position] != ")":
                result.append(term())
            if position == len(tokens):
                raise ValueError("Unclosed SMT expression")
            position += 1
            return result
        if token == ")":
            raise ValueError("Unexpected closing parenthesis")
        return token

    result = term()
    if position != len(tokens):
        raise ValueError("Trailing SMT expression")
    return result


def smt(value):
    if isinstance(value, list):
        return "(" + " ".join(map(smt, value)) + ")"
    if isinstance(value, bool):
        return str(value).lower()
    if isinstance(value, int) and value < 0:
        return f"(- {-value})"
    return str(value)


def literal(text):
    if text in ("true", "false"):
        return text == "true"
    if re.fullmatch(r"-?\d+", text):
        return int(text)
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*!val!\d+", text):
        return text
    raise ValueError(f"Unsupported native-model value: {text!r}")


class NativeModel:
    """Fail-closed evaluator for this capture's flat Int/Bool/uninterpreted tables.

    This is deliberately not a general parser for arbitrary Z3 model dumps.
    Every answer is independently checked against Z3 before an experiment runs.
    """

    def __init__(self, fixture):
        self.native = fixture["model"]
        self.constants = {}
        self.functions = {}
        self.signatures = {}
        for declaration in fixture["declarations"]:
            node = parse(declaration)
            if node[0] == "declare-fun":
                self.signatures[node[1]] = (node[2], node[3])
        active = None
        for raw in self.native.splitlines():
            line = raw.strip()
            if not line:
                continue
            if line == "}":
                if active is None or "default" not in self.functions[active]:
                    raise ValueError("Function table has no default")
                active = None
                continue
            left, separator, right = line.partition(" -> ")
            if not separator:
                raise ValueError(f"Unsupported native model line: {line!r}")
            if active:
                table = self.functions[active]
                if left == "else":
                    if "default" in table:
                        raise ValueError("Duplicate table default")
                    table["default"] = literal(right)
                else:
                    arguments = tuple(map(literal, left.split()))
                    if len(arguments) != len(self.signatures[active][0]):
                        raise ValueError("Unexpected table arity")
                    if arguments in table["entries"]:
                        raise ValueError("Duplicate table entry")
                    table["entries"][arguments] = literal(right)
            else:
                if not ATOM.fullmatch(left) or left in self.constants or left in self.functions:
                    raise ValueError(f"Unsupported or duplicate symbol: {left!r}")
                if right == "{":
                    if left not in self.signatures:
                        raise ValueError(f"Missing signature for {left}")
                    active = left
                    self.functions[left] = {"entries": {}}
                else:
                    self.constants[left] = literal(right)
        if active:
            raise ValueError("Unclosed native function table")

    def evaluate(self, expression, used=None):
        node = parse(expression) if isinstance(expression, str) else expression
        if not isinstance(node, list):
            if node in self.constants:
                if used is not None:
                    used["constants"].add(node)
                return self.constants[node]
            return literal(node)
        op, *arguments = node
        values = [self.evaluate(a, used) for a in arguments]
        if op in self.functions:
            key = tuple(values)
            table = self.functions[op]
            if len(values) != len(self.signatures[op][0]):
                raise ValueError("Function arity mismatch")
            if used is not None:
                used["functions"].setdefault(op, set()).add(key)
            return table["entries"].get(key, table["default"])
        if op == "=" and len(values) == 2:
            return values[0] == values[1]
        if op == "not" and len(values) == 1 and type(values[0]) is bool:
            return not values[0]
        if op == "=>" and len(values) == 2 and all(type(v) is bool for v in values):
            return not values[0] or values[1]
        if op == "+" and values and all(type(v) is int for v in values):
            return sum(values)
        raise ValueError(f"Unsupported expression: {smt(node)}")

    def relevant(self, expressions):
        used = {"constants": set(), "functions": {}}
        for expression in expressions:
            self.evaluate(expression, used)
        lines = [f"{k} -> {smt(v)}" for k, v in self.constants.items() if k in used["constants"]]
        for name, table in self.functions.items():
            if name not in used["functions"]:
                continue
            lines.append(name + " -> {")
            for arguments, value in table["entries"].items():
                if arguments in used["functions"][name]:
                    lines.append("  " + " ".join(map(smt, arguments)) + " -> " + smt(value))
            lines.extend(["  else -> " + smt(table["default"]), "}"])
        return "\n".join(lines) + "\n"

    def tables(self):
        return {"constants": self.constants, "functions": {
            name: {"entries": [{"arguments": list(k), "value": v} for k, v in table["entries"].items()],
                   "default": table["default"]}
            for name, table in self.functions.items()}}

    def aliases(self):
        # Group named constants only, without evaluating any question expression.
        # Python equates True with 1, so include the value's type in the key.
        groups = {}
        for name, value in self.constants.items():
            key = (type(value).__name__, value)
            groups.setdefault(key, {"value": value, "symbols": []})["symbols"].append(name)
        return {"meaning": "Complete inverse index of modeled named constants. Symbols in each group denote the same value. This does not equate distinct values, evaluate compound terms, or change function entries/defaults.",
                "groups": list(groups.values())}

    def smt_definitions(self):
        values = list(self.constants.values())
        for table in self.functions.values():
            values.append(table["default"])
            for arguments, value in table["entries"].items():
                values.extend([*arguments, value])
        domains = sorted({v for v in values if isinstance(v, str)})
        sorts = sorted({v.split("!val!")[0] for v in domains})
        lines = [f"(declare-sort {sort} 0)" for sort in sorts]
        for sort in sorts:
            members = [v for v in domains if v.split("!val!")[0] == sort]
            lines.extend(f"(declare-fun {v} () {sort})" for v in members)
            if len(members) > 1:
                lines.append("(assert (distinct " + " ".join(members) + "))")
        for name, value in self.constants.items():
            sort = "Bool" if type(value) is bool else "Int" if type(value) is int else value.split("!val!")[0]
            lines.append(f"(define-fun {name} () {sort} {smt(value)})")
        for name, table in self.functions.items():
            inputs, output = self.signatures[name]
            parameters = " ".join(f"(x{i} {sort})" for i, sort in enumerate(inputs))
            body = smt(table["default"])
            for arguments, value in reversed(list(table["entries"].items())):
                tests = " ".join(f"(= x{i} {smt(v)})" for i, v in enumerate(arguments))
                body = f"(ite (and {tests}) {smt(value)} {body})"
            lines.append(f"(define-fun {name} ({parameters}) {output} {body})")
        return "\n".join(lines)


def preservation(array="b@0", index="i@0", value="(Read_Int_Int a@0 i@0)", read_index="Z@3"):
    return f"(=> (not (= {index} {read_index})) (= (Read_Int_Int (Write_Int_Int {array} {index} {value}) {read_index}) (Read_Int_Int {array} {read_index})))"


def suite():
    """Expressions are public stimuli; the evaluator generates the private key."""
    probes = []

    def add(identifier, category, instruction, expressions, labels, mode="value"):
        probes.append(dict(id=identifier, category=category, instruction=instruction,
                           expressions=expressions, labels=labels, mode=mode))

    numeric = ["0", "1", "7", "8", "13"]
    add("symbol", "lookup", "What is the value of i@0?", ["i@0"], numeric)
    add("explicit-read", "lookup", "Evaluate (Read_Int_Int b@0 Z@3).", ["(Read_Int_Int b@0 Z@3)"], numeric)
    add("default-read", "default", "Evaluate (Read_Int_Int b@1 Z@3).", ["(Read_Int_Int b@1 Z@3)"], numeric)
    nested = "(Read_Int_Int (Write_Int_Int b@0 i@0 (Read_Int_Int a@0 i@0)) Z@3)"
    add("nested-read", "composition", "Evaluate " + nested + ".", [nested], numeric)
    one = "(Read_Int_Int (Write_Int_Int b@0 i@0 1) Z@3)"
    add("nested-control", "composition", "Evaluate " + one + ".", [one], numeric)
    add("unequal-indices", "logic", "Evaluate (not (= i@0 Z@3)).", ["(not (= i@0 Z@3))"], ["true", "false"])
    formulas = [preservation(), preservation(value="1"), preservation(value="0"), preservation(read_index="i@0")]
    # Equal numbers of true and false complete-formula controls.
    formulas += ["(= (Read_Int_Int b@0 Z@3) (Read_Int_Int b@1 Z@3))",
                 "(= (Read_Int_Int a@0 i@0) 7)"]
    for i, formula in enumerate(formulas):
        add(f"classify-{i + 1}", "classification", "Evaluate the COMPLETE formula in the supplied interpretation: " + formula,
            [formula], ["true", "false"])
    add("compare-instances", "comparison", "Which COMPLETE axiom instance evaluates to false? Exactly one option does.",
        [formulas[i] for i in [0, 1, 3]], [formulas[i] for i in [0, 1, 3]], "false-option")
    values = ["0", "1", "(Read_Int_Int a@0 i@0)"]
    add("choose-value", "binding", "For write-does-not-overwrite, fix a=b@0, idx=i@0, c=Z@3. "
        "Choose val making this COMPLETE formula false: "
        "(=> (not (= i@0 Z@3)) (= (Read_Int_Int (Write_Int_Int b@0 i@0 val) Z@3) (Read_Int_Int b@0 Z@3))). "
        "Only val may change.", [preservation(value=v) for v in values], values, "false-option")
    probes[-1]["binding_context"] = {
        "option_sort": "Int",
        "fixed_bindings": {
            "a": {"term": "b@0", "sort": "Array_Int_Int"},
            "idx": {"term": "i@0", "sort": "Int"},
            "c": {"term": "Z@3", "sort": "Int"},
        },
    }
    return probes


def answer_key(model, probe):
    values = [model.evaluate(e) for e in probe["expressions"]]
    if probe["mode"] == "value":
        matches = [i for i, label in enumerate(probe["labels"]) if label == smt(values[0])]
    else:
        matches = [i for i, value in enumerate(values) if value is False]
    if not matches or (probe["id"] != "choose-value" and len(matches) != 1):
        raise ValueError(f"{probe['id']}: unexpected correct options: {matches}")
    return matches, values


def binding_term_interpretations(model, probe, order):
    """Annotate every substitution term, never the instantiated formulas."""
    context = probe.get("binding_context")
    if probe["category"] != "binding" or context is None:
        raise ValueError("Term-value context requires a binding probe (use --question choose-value)")

    def interpret(term, sort):
        try:
            evaluation = {"status": "known", "value": smt(model.evaluate(term))}
        except ValueError:
            # No model completion or guessed value for unsupported/unmodeled terms.
            evaluation = {"status": "unknown"}
        return {"term": term, "sort": sort, "evaluation": evaluation}

    return {
        "meaning": "Current interpretation of EVERY offered substitution term and fixed binding. "
                   "Known values were evaluated in the supplied abstract model, without assuming array axioms. "
                   "Unknown means no value is supplied, not false. These values do not evaluate the complete "
                   "instantiated axiom or identify a preferred option. Choose the original option ID, not a model-domain value.",
        "options": {f"o{i}": interpret(probe["labels"][j], context["option_sort"])
                    for i, j in enumerate(order)},
        "fixed_bindings": {slot: interpret(binding["term"], binding["sort"])
                           for slot, binding in context["fixed_bindings"].items()},
    }


def verify_oracle(model, probes, executable, verify_binding_terms=False):
    expressions = {e for p in probes for e in p["expressions"]}
    if verify_binding_terms:
        for probe in probes:
            annotations = binding_term_interpretations(model, probe, range(len(probe["labels"])))
            expressions.update(entry["term"]
                               for group in ("options", "fixed_bindings")
                               for entry in annotations[group].values()
                               if entry["evaluation"]["status"] == "known")
    expressions = sorted(expressions)
    script = model.smt_definitions() + "\n(check-sat)\n"
    for expression in expressions:
        value = smt(model.evaluate(expression))
        script += f"(push)\n(assert (not (= {expression} {value})))\n(check-sat)\n(pop)\n"
    result = subprocess.run([executable, "-in", "-smt2"], input=script, text=True,
                            capture_output=True, timeout=30, check=True)
    if result.stdout.split() != ["sat"] + ["unsat"] * len(expressions):
        raise ValueError("Z3 disagreed with the evaluator or rejected the model: " + result.stdout[:1000])
    version = subprocess.run([executable, "-version"], text=True, capture_output=True, check=True, timeout=10).stdout.strip()
    return {"expressions_checked": len(expressions), "z3_version": version}


def request_for(model, fixture, probe, presentation, order, provider_model, anonymize=False, task_context="baseline", vmt_source=None, ablation=None):
    if ablation is not None:
        if ablation not in ABLATIONS + BINDING_ABLATIONS or presentation != "native" or anonymize or vmt_source is None:
            raise ValueError("Ablations require a known variant, native presentation, full VMT, and original symbols")
        task_context = "property-directed" if ablation in BINDING_ABLATIONS else "procedural"
    if anonymize and vmt_source is not None:
        raise ValueError("Verbatim VMT context cannot be combined with symbol anonymization")
    description = {
        "native": "Unmodified native Z3 interpretation; omitted symbols are unknown.",
        "relevant": "Reduced native interpretation retaining entries needed for ALL options in this question, plus defaults. Only evaluate the requested expressions.",
        "tables": "Full interpretation as explicit entries and defaults. Use default only if no argument tuple matches.",
    }
    payload = model.native if presentation == "native" else model.relevant(probe["expressions"]) if presentation == "relevant" else model.tables()
    request = {"model": provider_model, "state": {
        "task": "Evaluate the supplied interpretation literally. Read/Write are UNINTERPRETED functions: do not assume intended array laws. "
                "Resolve symbols, evaluate inner applications first, and use function defaults when no explicit entry matches. "
                "An implication with a false antecedent is true. Return the requested multiple-choice answer.",
        "model_format": description[presentation], "model": payload,
        "declarations": fixture["declarations"],
        "options": {f"o{i}": probe["labels"][j] for i, j in enumerate(order)},
    }, "questions": {"answer": {"type": "choice", "instructions": probe["instruction"] + " Choose an option ID from state.options, which gives each option's value or expression.",
                                  "criteria": {f"o{i}": None for i in range(len(order))}}}}
    if task_context == "refinement":
        request["state"]["task"] = REFINEMENT_CONTEXT + request["state"]["task"]
    elif task_context == "falsification":
        request["state"]["task"] = FALSIFICATION_PROMPT
    elif task_context == "property-directed":
        if vmt_source is None:
            raise ValueError("property-directed requires the original VMT")
        request["state"]["task"] = PROPERTY_DIRECTED_PROMPT
    elif task_context == "procedural":
        request["state"]["task"] = PROCEDURAL_PROMPT
    elif task_context != "baseline":
        raise ValueError(f"Unknown task context: {task_context}")
    if ablation == "procedural-examples":
        request["state"]["worked_examples"] = WORKED_EXAMPLES
    elif ablation == "procedural-aliases":
        request["state"]["model_aliases"] = model.aliases()
    elif ablation == "property-directed-term-values":
        request["state"]["term_interpretations"] = binding_term_interpretations(model, probe, order)
    if vmt_source is not None:
        request["state"]["problem"] = {
            "format": "VMT", "source": vmt_source,
            "notation": "This is the complete original verification problem. :init marks the initial condition, "
                        ":trans the transition relation, :invar-property the property, and :next the current/next variable mapping. "
                        "For Int arrays, select/store in the VMT correspond to Read_Int_Int/Write_Int_Int in the abstract model. "
                        "x@N denotes x at absolute frame N; the :next variable denotes its value at the following frame. "
                        "The original problem uses array semantics, while the supplied abstract function tables may violate them.",
        }
    if anonymize:
        # Change only model symbols, consistently in model, declarations, and task.
        names = sorted(set(model.constants) | set(model.functions))
        mapping = {name: f"symbol_{i:03}" for i, name in enumerate(names)}
        pattern = re.compile(r"[A-Za-z_][A-Za-z0-9_@!+.-]*")

        def rename(value):
            if isinstance(value, str):
                return pattern.sub(lambda m: mapping.get(m[0], m[0]), value)
            if isinstance(value, dict):
                return {rename(k): rename(v) for k, v in value.items()}
            if isinstance(value, list):
                return [rename(v) for v in value]
            return value

        request["state"] = rename(request["state"])
        request["questions"] = rename(request["questions"])
    return request


def grade(response, correct, offered):
    answers = response.get("answers", {})
    answer = answers.get("answer", {}) if isinstance(answers, dict) else {}
    if not isinstance(answer, dict):
        answer = {}
    choice = answer.get("choice")
    if answer.get("type") != "choice" or not isinstance(choice, str) or choice not in offered:
        return {"status": "invalid", "correct": False, "error": "Missing or unoffered choice"}
    probabilities = answer.get("probabilities")
    valid = (isinstance(probabilities, dict) and set(probabilities) == set(offered)
             and all(type(v) in (int, float) and math.isfinite(v) and 0 <= v <= 1 for v in probabilities.values()))
    return {"status": "answered", "choice": choice, "correct": choice in correct,
            "correct_probability": sum(probabilities[c] for c in correct) if valid else None,
            "probability_mass": sum(probabilities.values()) if valid else None,
            "probabilities_valid": valid}


def cost(response, input_rate, output_rate):
    usage = response.get("usage", {})
    if not isinstance(usage, dict):
        usage = {}
    counts = [usage.get("input_tokens"), usage.get("output_tokens", 0 if output_rate == 0 else None)]
    estimate = None
    if all(type(n) is int and n >= 0 for n in counts):
        estimate = (counts[0] * input_rate + counts[1] * output_rate) / 1_000_000
    return {"estimated_usd": estimate, "usage": usage, "input_usd_per_million": input_rate,
            "output_usd_per_million": output_rate}


class JevClient:
    def __init__(self, key, timeout):
        self.key = key
        self.connection = http.client.HTTPSConnection("api.typesafe.ai", timeout=timeout)

    def decide(self, request):
        self.connection.request("POST", "/v1/systemone", json.dumps(request).encode(),
                                {"Authorization": "Bearer " + self.key, "Content-Type": "application/json"})
        response = self.connection.getresponse()
        body = response.read(4 * 1024 * 1024 + 1)
        if len(body) > 4 * 1024 * 1024:
            raise ValueError("Jev response exceeds 4 MiB")
        if response.status != 200:
            raise ValueError(f"Jev HTTP {response.status}: {body.decode(errors='replace')[:1000]}")
        def reject_constant(value):
            raise ValueError(f"Non-finite JSON number: {value}")

        result = json.loads(body, parse_constant=reject_constant)
        if not isinstance(result, dict):
            raise ValueError("Jev returned a non-object response")
        return result

    def close(self):
        self.connection.close()


def api_key(env_file):
    if os.environ.get("JEV_API_KEY", "").strip():
        return os.environ["JEV_API_KEY"].strip()
    if env_file.exists():
        for line in env_file.read_text().splitlines():
            match = re.fullmatch(r"\s*(?:export\s+)?JEV_API_KEY\s*=\s*(.*?)\s*", line)
            if match:
                value = match[1]
                if len(value) >= 2 and value[0] == value[-1] and value[0] in "\"'":
                    value = value[1:-1]
                else:
                    value = value.split(" #", 1)[0].strip()
                if value:
                    return value
    raise ValueError("Set JEV_API_KEY or provide an .env file containing it")


def summarize(path):
    requests, results = {}, {}
    partial = False
    lines = path.read_text().splitlines()
    for i, line in enumerate(lines):
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            if i != len(lines) - 1:
                raise
            partial = True
            break
        if row["event"] == "request":
            requests[row["query_id"]] = row
        elif row["event"] == "result":
            results[row["query_id"]] = row
    groups = defaultdict(list)
    for identifier, request in requests.items():
        if request["live"]:
            groups[(request.get("ablation") or request.get("task_context", "baseline"), request["presentation"], request["category"])].append({
                **results.get(identifier, {"status": "interrupted"}), "chance_accuracy": request["chance_accuracy"]})
    breakdown = []
    for (variant, presentation, category), rows in sorted(groups.items()):
        probabilities = [r["correct_probability"] for r in rows if r.get("correct_probability") is not None]
        answered = sum(r["status"] == "answered" for r in rows)
        correct = sum(r.get("correct", False) for r in rows)
        breakdown.append(dict(variant=variant, presentation=presentation, category=category, queries=len(rows),
                              outcomes=dict(Counter(r["status"] for r in rows)), correct=correct,
                              accuracy_all_queries=correct / len(rows),
                              accuracy_answered=correct / answered if answered else None,
                              chance_accuracy=sum(r["chance_accuracy"] for r in rows) / len(rows),
                              mean_correct_probability=sum(probabilities) / len(probabilities) if probabilities else None))
    live = [q for q in requests.values() if q["live"]]
    costs = [results[q["query_id"]]["cost"]["estimated_usd"] for q in live
             if q["query_id"] in results and results[q["query_id"]]["cost"]["estimated_usd"] is not None]
    input_tokens = [r.get("response", {}).get("usage", {}).get("input_tokens") for r in results.values()
                    if isinstance(r.get("response", {}).get("usage", {}), dict)]
    input_tokens = [n for n in input_tokens if type(n) is int and n >= 0]
    return dict(requests=len(requests), live_requests=len(live), results=len(results), partial_final_record=partial,
                max_request_bytes=max((q.get("request_bytes", 0) for q in requests.values()), default=0),
                reported_input_tokens_total=sum(input_tokens),
                reported_input_tokens_min=min(input_tokens, default=None),
                reported_input_tokens_max=max(input_tokens, default=None),
                known_estimated_usd=sum(costs), queries_with_unknown_cost=len(live) - len(costs),
                client_elapsed_secs=sum(r.get("elapsed_secs", 0) for r in results.values()), breakdown=breakdown)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    report = commands.add_parser("summarize", help="Summarize results, including interrupted runs")
    report.add_argument("log", type=Path)
    run = commands.add_parser("run", help="Write offline requests; add --live to call Jev")
    run.add_argument("--fixture", type=Path, default=HERE / "depth3.json")
    run.add_argument("--output", type=Path, required=True, help="New JSONL file; never overwritten")
    run.add_argument("--presentation", nargs="+", choices=["native", "relevant", "tables"], default=["native"])
    run.add_argument("--question", nargs="+", choices=[p["id"] for p in suite()])
    run.add_argument("--repeats", type=int, default=1)
    run.add_argument("--seed", type=int, default=0)
    run.add_argument("--shuffle-options", action="store_true")
    run.add_argument("--anonymize", action="store_true", help="Consistently rename constant/function symbols")
    run.add_argument("--vmt", type=Path, help="Include this complete original VMT verbatim, with notation mapping")
    run.add_argument("--task-context", choices=["baseline", "refinement", "falsification", "property-directed", "procedural"], default="baseline",
                     help="Select the task prompt without changing the model or options")
    run.add_argument("--ablation", nargs="+", choices=list(dict.fromkeys(ABLATIONS + BINDING_ABLATIONS)),
                     help="Interleave paired variants on the full native model and VMT; overrides task context")
    run.add_argument("--live", action="store_true")
    run.add_argument("--model", default="jev-latest")
    run.add_argument("--timeout", type=float, default=30)
    run.add_argument("--max-queries", type=int, default=100)
    run.add_argument("--input-usd-per-million", type=float, default=0.042)
    run.add_argument("--output-usd-per-million", type=float, default=0)
    run.add_argument("--env-file", type=Path, default=HERE.parent.parent / ".env")
    run.add_argument("--z3", default=shutil.which("z3"), help="Z3 executable used to check the answer key")
    args = parser.parse_args(argv)
    if args.command == "summarize":
        print(json.dumps(summarize(args.log), indent=2))
        return 0
    if not args.z3:
        parser.error("Z3 is required to verify answers; provide --z3 /path/to/z3")
    if args.repeats < 1 or args.max_queries < 1 or not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error("Repeats, max queries, and timeout must be positive")
    if any(not math.isfinite(r) or r < 0 for r in [args.input_usd_per_million, args.output_usd_per_million]):
        parser.error("Prices must be finite and nonnegative")
    if args.output.exists():
        parser.error("Output already exists; choose a new JSONL file")
    if args.vmt and args.anonymize:
        parser.error("--vmt cannot be combined with --anonymize: the original source must retain consistent names")
    if args.task_context == "property-directed" and not args.vmt:
        parser.error("--task-context property-directed requires --vmt")
    if args.ablation and (not args.vmt or args.anonymize or args.presentation != ["native"] or args.task_context != "baseline"):
        parser.error("--ablation requires --vmt, native presentation, original symbols, and no --task-context override")
    vmt_bytes = args.vmt.read_bytes() if args.vmt else None
    vmt_source = vmt_bytes.decode("utf-8") if vmt_bytes is not None else None
    fixture_bytes = args.fixture.read_bytes()
    fixture = json.loads(fixture_bytes)
    model = NativeModel(fixture)
    probes = [p for p in suite() if args.question is None or p["id"] in args.question]
    presentations = list(dict.fromkeys(args.presentation))
    variants = list(dict.fromkeys(args.ablation)) if args.ablation else [None]
    verify_binding_terms = "property-directed-term-values" in variants
    if verify_binding_terms and any(p["category"] != "binding" or "binding_context" not in p for p in probes):
        parser.error("property-directed-term-values requires binding probes; use --question choose-value")
    count = len(probes) * len(presentations) * args.repeats * len(variants)
    if count > args.max_queries:
        parser.error(f"Experiment needs {count} requests, exceeding --max-queries {args.max_queries}")
    keys = {p["id"]: answer_key(model, p) for p in probes}
    verification = verify_oracle(model, probes, args.z3, verify_binding_terms=verify_binding_terms)
    jobs = [(p, view, trial, variant) for trial in range(args.repeats) for p in probes for view in presentations for variant in variants]
    random.Random(args.seed).shuffle(jobs)
    key = api_key(args.env_file) if args.live else None
    client = JevClient(key, args.timeout) if args.live else None
    failed = False
    try:
        with args.output.open("x") as log:
            def record(row):
                log.write(json.dumps(row, allow_nan=False) + "\n")
                log.flush()

            record({"event": "experiment", "schema_version": 1, "fixture_sha256": hashlib.sha256(fixture_bytes).hexdigest(),
                    "runner_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                    "vmt_sha256": hashlib.sha256(vmt_bytes).hexdigest() if vmt_bytes is not None else None,
                    "vmt_bytes": len(vmt_bytes) if vmt_bytes is not None else None,
                    "provenance": fixture["provenance"], "verification": verification,
                    "configuration": {k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()},
                    "planned_queries": count})
            for query_id, (probe, view, trial, variant) in enumerate(jobs, 1):
                order = list(range(len(probe["labels"])))
                if args.shuffle_options:
                    random.Random(f"{args.seed}:{trial}:{probe['id']}").shuffle(order)
                correct_indices, values = keys[probe["id"]]
                correct = [f"o{order.index(index)}" for index in correct_indices]
                request = request_for(model, fixture, probe, view, order, args.model, args.anonymize, args.task_context, vmt_source, variant)
                record({"event": "request", "query_id": query_id, "live": args.live,
                        "presentation": view, "question": probe["id"], "category": probe["category"], "trial": trial,
                        "task_context": "property-directed" if variant in BINDING_ABLATIONS else "procedural" if variant else args.task_context,
                        "ablation": variant,
                        "expected_choices": correct, "oracle_values": values, "request": request,
                        "chance_accuracy": len(correct) / len(order),
                        "request_bytes": len(json.dumps(request).encode())})
                if client is None:
                    continue
                start = time.monotonic()
                response = {}
                try:
                    response = client.decide(request)
                    scored = grade(response, correct, request["questions"]["answer"]["criteria"])
                except (OSError, ValueError, http.client.HTTPException) as error:
                    scored = {"status": "error", "error": str(error)}
                    failed = True
                record({"event": "result", "query_id": query_id, "response": response,
                        "elapsed_secs": time.monotonic() - start, **scored,
                        "cost": cost(response, args.input_usd_per_million, args.output_usd_per_million)})
                print(f"{query_id}/{count} {variant or view} {probe['id']}: {scored['status']} correct={scored.get('correct')}", file=sys.stderr)
                if failed:
                    break  # No automatic retries, including potentially billable failures.
    finally:
        if client:
            client.close()
    print(json.dumps(summarize(args.output), indent=2))
    return 1 if failed else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1)
