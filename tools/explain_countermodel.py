#!/usr/bin/env python3
"""Print a Yardbird counter-model trace, or one root-to-node explanation."""
import argparse
import gzip
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("result", type=Path, help="Yardbird JSON result, optionally .gz")
    parser.add_argument("--depth", type=int)
    parser.add_argument("--step", type=int, help="refinement step")
    parser.add_argument("--node", type=int, help="show just the ancestry of this node")
    args = parser.parse_args()
    opener = gzip.open if args.result.suffix == ".gz" else open
    with opener(args.result, "rt") as stream:
        result = json.load(stream)
    records = [r for r in result.get("profiling", {}).get("cost_records", [])
               if r.get("countermodel_trace")
               and (args.depth is None or r.get("bmc_depth") == args.depth)
               and (args.step is None or r.get("refinement_step") == args.step)]
    if not records:
        parser.error("no matching trace; run abstract VMT with --countermodel-trace-work N --json-output")
    record = records[-1]
    trace = record["countermodel_trace"]
    nodes = {node["id"]: node for node in trace["nodes"]}
    selected = set(nodes)
    if args.node is not None:
        if args.node not in nodes:
            parser.error(f"node {args.node} is not in this trace")
        selected = set()
        current = args.node
        while current is not None:
            selected.add(current)
            current = nodes[current]["parent"]
    print(f"Depth {trace['depth']}, refinement {record['refinement_step']}, model {trace['model_version']}")
    print(f"Work: {trace['work']}; budget exhausted: {trace['budget_exhausted']}")
    for node in trace["nodes"]:
        if node["id"] not in selected:
            continue
        print(f"\n[{node['id']}] parent={node['parent']} {node['reason']}")
        print(f"  {node['expression']}\n  model value: {node['model_value']}; status: {node['status']}")
        for condition in node["conditions"]:
            print(f"  observed: {condition['expression']} = {condition['value']}")
        if node.get("lemma"):
            lemma = node["lemma"]
            print(f"  {lemma['rule']}: {lemma['formula']}")
            print(f"  lemma in model: {lemma['model_value']}")


if __name__ == "__main__":
    main()
