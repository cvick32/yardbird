#!/usr/bin/env python3
"""Generate auditable, extensionally equivalent lambda-free VMT companions.

Only commands containing lambdas are rewritten. No new free symbols, state,
assumptions, finite domains, or solver options are introduced. See
examples/distributed_protocols/ENCODINGS.md for the encoding rules.
"""

import argparse
import concurrent.futures
import hashlib
import json
import re
import subprocess
from pathlib import Path


TOKEN = re.compile(r'\s+|;[^\n]*|\|[^|]*\||"(?:[^"]|"")*"|[()]|[^\s()]+')
BINDERS = {"lambda", "forall", "exists"}


def parse_spans(source):
    tokens = [(m.group(), m.start(), m.end()) for m in TOKEN.finditer(source)
              if not m.group().isspace() and not m.group().startswith(";")]
    position = 0

    def one():
        nonlocal position
        token, start, end = tokens[position]
        position += 1
        if token == ")":
            raise ValueError("unexpected closing parenthesis")
        if token != "(":
            return token, start, end
        children = []
        while position < len(tokens) and tokens[position][0] != ")":
            children.append(one()[0])
        if position == len(tokens):
            raise ValueError("unterminated expression")
        end = tokens[position][2]
        position += 1
        return children, start, end

    result = []
    while position < len(tokens):
        result.append(one())
    return result


def dump(term):
    return "(" + " ".join(map(dump, term)) + ")" if isinstance(term, list) else term


def pretty(term, indent=0):
    flat = dump(term)
    if not isinstance(term, list) or len(flat) + indent <= 100:
        return flat
    # Keep operators and binder declarations on the first line.
    head = 2 if term and term[0] in ("forall", "exists", "lambda", "let") else 1
    if term and term[0] == "define-fun":
        head = 4
    first = "(" + " ".join(dump(t) for t in term[:head])
    return first + "".join("\n" + " " * (indent + 2) + pretty(t, indent + 2)
                           for t in term[head:]) + ")"


def contains_lambda(term):
    return isinstance(term, list) and (
        bool(term) and term[0] == "lambda" or any(contains_lambda(t) for t in term))


def atoms(term):
    if isinstance(term, str):
        return {term}
    return set().union(*(atoms(t) for t in term))


def symbol_key(symbol):
    return symbol[1:-1] if symbol.startswith("|") and symbol.endswith("|") else symbol


def free_vars(term):
    if isinstance(term, str):
        return {symbol_key(term)}
    if not term:
        return set()
    if isinstance(term[0], str) and term[0] in BINDERS:
        return free_vars(term[2]) - {symbol_key(v) for v, _ in term[1]}
    if term[0] == "let":
        return (free_vars(term[2]) - {symbol_key(v) for v, _ in term[1]}) | set().union(
            *(free_vars(value) for _, value in term[1]))
    return set().union(*(free_vars(t) for t in term))


class Encoder:
    def __init__(self, commands):
        # SMT quoting does not create a different symbol: foo and |foo| alias.
        self.used = {symbol_key(symbol) for symbol in atoms(commands)}
        self.serial = 0
        self.functions = {}
        self.sort_declarations = []
        self.declarations = []
        self.obligations = []
        for command in commands:
            if command[0] == "declare-sort":
                self.sort_declarations.append(command)
            elif command[0] == "declare-fun":
                self.functions[symbol_key(command[1])] = command[3]
                self.declarations.append(command)
            elif command[0] == "declare-const":
                self.functions[symbol_key(command[1])] = command[2]
                self.declarations.append(command)
            elif command[0] == "define-fun":
                # VMT has multiple property definitions with the same name;
                # these annotations are not ordinary SMT function declarations.
                self.functions[symbol_key(command[1])] = command[3]

    def fresh(self):
        while True:
            symbol = f"|encoding.index.{self.serial}|"
            self.serial += 1
            key = symbol[1:-1]
            if key not in self.used:
                self.used.add(key)
                return symbol

    def expand(self, term, replacements=None):
        """Simultaneous let expansion and capture-avoiding substitution."""
        replacements = {symbol_key(k): v for k, v in (replacements or {}).items()}
        if isinstance(term, str):
            return replacements.get(symbol_key(term), term)
        if not term:
            return term
        op = term[0]
        if op == "let":
            values = {symbol_key(v): self.expand(value, replacements) for v, value in term[1]}
            return self.expand(term[2], {**replacements, **values})
        if isinstance(op, str) and op in BINDERS:
            scoped = {k: v for k, v in replacements.items()
                      if k not in {symbol_key(name) for name, _ in term[1]}}
            captured = set().union(*(free_vars(value) for value in scoped.values()))
            bindings = []
            for name, sort in term[1]:
                new_name = self.fresh() if symbol_key(name) in captured else name
                bindings.append([new_name, sort])
                if new_name != name:
                    scoped[symbol_key(name)] = new_name
            return [op, bindings, self.expand(term[2], scoped)]
        if op == "!":
            return [op, self.expand(term[1], replacements), *term[2:]]
        return [self.expand(t, replacements) for t in term]

    def sort(self, term, scope):
        scope = {symbol_key(name): sort for name, sort in scope.items()}
        if isinstance(term, str):
            if symbol_key(term) in scope:
                return scope[symbol_key(term)]
            if symbol_key(term) in self.functions:
                return self.functions[symbol_key(term)]
            if term in ("true", "false"):
                return "Bool"
            if re.fullmatch(r"[0-9]+", term):
                return "Int"
            raise ValueError(f"unknown sort for {term}")
        op = term[0]
        if isinstance(op, list):
            if op[:2] == ["as", "const"]:
                return op[2]
            raise ValueError(f"unsupported indexed application {dump(term)}")
        if op == "lambda":
            if len(term[1]) != 1:
                raise ValueError("multi-index lambdas require a separate encoding")
            name, index_sort = term[1][0]
            return ["Array", index_sort, self.sort(term[2], {**scope, name: index_sort})]
        if op == "select":
            array = self.sort(term[1], scope)
            if not isinstance(array, list) or array[0] != "Array":
                raise ValueError(f"select of non-array: {dump(term)}")
            return array[2]
        if op == "store":
            return self.sort(term[1], scope)
        if op == "ite":
            return self.sort(term[2], scope)
        if op == "!":
            return self.sort(term[1], scope)
        if op in {"=", "distinct", "and", "or", "not", "=>", "xor", "forall", "exists",
                  "<", "<=", ">", ">="}:
            return "Bool"
        if symbol_key(op) in self.functions:
            return self.functions[symbol_key(op)]
        if op in {"+", "-", "*", "div", "mod"}:
            return "Int"
        raise ValueError(f"unknown sort for {dump(term)}")

    def read(self, array, index):
        if not contains_lambda(array):
            return ["select", array, index]
        if array[0] == "lambda":
            if len(array[1]) != 1:
                raise ValueError("multi-index lambda")
            return self.expand(array[2], {array[1][0][0]: index})
        if array[0] == "store":
            return ["ite", ["=", index, array[2]], array[3], self.read(array[1], index)]
        if array[0] == "ite":
            return ["ite", array[1], self.read(array[2], index), self.read(array[3], index)]
        raise ValueError(f"lambda in unsupported array expression: {dump(array)}")

    def rewrite(self, term, scope=None):
        scope = scope or {}
        if isinstance(term, str) or not term:
            return term
        op = term[0]
        if isinstance(op, str) and op in BINDERS:
            return [op, term[1], self.rewrite(term[2], {**scope, **dict(term[1])})]
        if op == "!":
            return [op, self.rewrite(term[1], scope), *term[2:]]
        # Qualified identifiers and their sort expressions are not terms.
        args = [self.rewrite(t, scope) for t in term[1:]]
        term = [op, *args]
        if op == "select" and contains_lambda(args[0]):
            return self.rewrite(self.read(args[0], args[1]), scope)
        if op == "=" and contains_lambda(args):
            if len(args) != 2:
                raise ValueError("lambda-bearing n-ary equality requires explicit handling")
            array_sort = self.sort(args[0], scope)
            if array_sort != self.sort(args[1], scope):
                raise ValueError(f"equality sort mismatch: {dump(term)}")
            if not isinstance(array_sort, list) or array_sort[0] != "Array":
                raise ValueError(f"lambda outside an array equality: {dump(term)}")
            index = self.fresh()
            body = ["=", self.read(args[0], index), self.read(args[1], index)]
            result = ["forall", [[index, array_sort[1]]],
                      self.rewrite(body, {**scope, index: array_sort[1]})]
            self.obligations.append((term, result, dict(scope)))
            return result
        return term

    def command(self, command):
        if command[0] == "assert":
            return ["assert", self.rewrite(self.expand(command[1]))]
        if command[0] == "define-fun":
            return [*command[:4], self.rewrite(self.expand(command[4]), dict(command[2]))]
        raise ValueError(f"lambda in unsupported command: {command[0]}")


def encode(source):
    spans = parse_spans(source)
    encoder = Encoder([term for term, _, _ in spans])
    changes = []
    for command, start, end in spans:
        if not contains_lambda(command):
            continue
        new = encoder.command(command)
        if contains_lambda(new):
            raise ValueError(f"uneliminated lambda in {command[:2]}")
        changes.append((start, end, pretty(new)))
    result = source
    for start, end, replacement in reversed(changes):
        result = result[:start] + replacement + result[end:]
    return result, encoder, len(changes)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("examples/distributed_protocols"))
    parser.add_argument("--check", action="store_true", help="verify companions match the generator")
    parser.add_argument("--audit-dir", type=Path, help="write per-rewrite SMT equivalence obligations")
    parser.add_argument("--verify", action="store_true", help="require Z3 UNSAT for every equivalence obligation")
    parser.add_argument("--binary", type=Path, default=Path("target/release/yardbird"))
    args = parser.parse_args()
    if args.verify and not args.audit_dir:
        parser.error("--verify requires --audit-dir")
    inventory = []
    obligations = []
    for path in sorted(args.root.glob("*/*.vmt")):
        if path.name.endswith(".encoding.vmt"):
            continue
        source_bytes = path.read_bytes()
        source = source_bytes.decode()
        rewritten, encoder, changed = encode(source)
        digest = hashlib.sha256(source_bytes).hexdigest()
        header = (f"; Lambda-free companion of {path.name}\n"
                  f"; Original SHA-256: {digest}\n"
                  "; Generated by scripts/encode_distributed_protocols.py.\n"
                  "; Array extensionality and capture-avoiding beta/let reduction only.\n"
                  "; No new free symbols, assumptions, domain bounds, or solver options.\n")
        target = path.with_suffix(".encoding.vmt")
        content = header + rewritten
        if args.check:
            if target.read_bytes().decode() != content:
                raise SystemExit(f"stale companion: {target}")
        else:
            target.write_text(content)
        if args.audit_dir:
            folder = args.audit_dir / path.stem
            folder.mkdir(parents=True, exist_ok=True)
            for index, (before, after, scope) in enumerate(encoder.obligations):
                equality = ["=", before, after]
                if scope:
                    equality = ["forall", [[k, v] for k, v in scope.items()], equality]
                commands = [["set-logic", "ALL"], *encoder.sort_declarations,
                            *encoder.declarations, ["assert", ["not", equality]], ["check-sat"]]
                obligation = folder / f"{index:03}.smt2"
                obligation.write_text("\n".join(map(dump, commands)) + "\n")
                obligations.append(obligation)
        inventory.append({"original": str(path), "encoding": str(target), "sha256": digest,
                          "changed_commands": changed, "extensionality_steps": len(encoder.obligations)})
    print(json.dumps(inventory, indent=2))
    if args.verify:
        def verify(path):
            try:
                result = subprocess.run(
                    [str(args.binary), "-f", str(path), "-s", "concrete", "--json-output"],
                    capture_output=True, text=True, timeout=10)
                data = json.loads(result.stdout) if result.returncode == 0 else {}
                checks = data.get("results", [])
                verdict = checks[0]["result"] if len(checks) == 1 else "error"
                return {"file": str(path), "result": verdict, "error": result.stderr}
            except (subprocess.TimeoutExpired, json.JSONDecodeError) as error:
                return {"file": str(path), "result": "error", "error": str(error)}

        with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
            verdicts = list(pool.map(verify, obligations))
        (args.audit_dir / "verification.json").write_text(json.dumps(verdicts, indent=2) + "\n")
        failed = [v for v in verdicts if v["result"] != "Unsat"]
        if failed:
            raise SystemExit(f"{len(failed)} equivalence obligations were not proved UNSAT")


if __name__ == "__main__":
    main()
