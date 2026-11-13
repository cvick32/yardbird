#!/usr/bin/env python3
"""Summarize disjoint driver timings separately from nested operation timings."""
import json, sys
from collections import Counter, defaultdict
from pathlib import Path

def analyze(path):
    d = json.loads(Path(path).read_text())
    p = d['profiling']
    driver = Counter()
    costs = Counter()
    counters = Counter()
    depths = {}
    operations = defaultdict(Counter)
    for r in p['driver_records']:
        driver.update(r['timing_secs'])
        a = depths.setdefault(r['bmc_depth'], dict(timing=Counter(), steps=0, instances=0))
        a['timing'].update(r['timing_secs'])
        a['steps'] += 1
        a['instances'] += r['unique_instances_after'] - r['unique_instances_before']
    solver = Counter()
    solver_depth = defaultdict(Counter)
    for r in p['solver_checks']:
        solver.update({k: v / 1000000000.0 for (k, v) in r['timing_ns'].items()})
        solver_depth[r['depth']].update(checks=1, raw_secs=r['timing_ns']['raw_check'] / 1000000000.0)
    traces = Counter()
    phases = defaultdict(Counter)
    for r in p['cost_records']:
        costs.update(r['timing_secs'])
        counters.update(r['counters'])
        for e in r['effort']:
            if e['kind'] != 'operation':
                continue
            a = operations[e['operation']]
            a.update(calls=1, secs=e['elapsed_secs'], selected=e['report']['selected'], empty_calls=int(e['report']['selected'] == 0), exhausted=int(e['report']['budget_exhausted']))
            if not e['report']['selected']:
                a['empty_secs'] += e['elapsed_secs']
        for (rule, ph) in r['quantifier_work'].items():
            for (phase, v) in ph.items():
                phases[phase].update(v['timing_secs'])
        t = r.get('countermodel_trace')
        if t:
            traces.update(calls=1, work=t['work'], nodes=len(t['nodes']), exhausted=int(t['budget_exhausted']))
            traces.update(Counter((n['status']['kind'] for n in t['nodes'])))
    for (depth, a) in depths.items():
        a['solver'] = solver_depth[depth]
    return dict(path=str(path), progress=d['run_progress'], run_timing=p['timing_secs'], driver=driver, depths=depths, solver=solver, operations=dict(operations), costs=costs, counters=counters, quantifier_phases=dict(phases), traces=traces, total_instances=d['total_instantiations_added'])
if __name__ == '__main__':
    print(json.dumps([analyze(p) for p in sys.argv[1:]], indent=2))
