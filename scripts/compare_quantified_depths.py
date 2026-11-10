#!/usr/bin/env python3
"""Compare verified BMC depth progress in a complete paired benchmark run.

A completed depth requires all property clauses, so depths 0..19 count as 20.
Started depths, counterexamples, and checks after the wall budget earn no credit.
Unknown/timeouts retain the depths they actually completed. No unbounded claim.
"""
import argparse
from collections import Counter
import csv
import itertools
import json
from pathlib import Path


def completed_times(row, target, budget):
    progress = row.get('progress') or {}
    depths = progress.get('depth_completions', [])
    if [d.get('depth') for d in depths] != list(range(len(depths))):
        raise ValueError(f"Non-contiguous completed depths: {row.get('artifact')}")
    if len(depths) > target:
        raise ValueError('Completed depths exceed target')
    expected = len(depths) - 1 if depths else None
    if progress.get('deepest_completed_depth') != expected:
        raise ValueError('Deepest completed depth disagrees with completion records')
    times = [float(d['elapsed_wall_secs']) for d in depths]
    if any(not (0 <= t < float('inf')) for t in times) or times != sorted(times):
        raise ValueError('Invalid completion times')
    if row['status'] == 'depth_limit' and (len(depths) != target or row.get('counterexample') is not False):
        raise ValueError('Invalid depth-limit success')
    return [t for t in times if t <= budget]


def status(row):
    if (row.get('progress') or {}).get('termination_reason') == 'solver_unknown':
        return 'unknown'
    if row['status'] in ('timeout', 'external_timeout'):
        return 'timeout'
    return row['status']


def compare(metadata, rows):
    variants = metadata['variant_order']
    paths = metadata['input_order']
    repeats, target, budget = metadata['repeat'], metadata['depth'], metadata['timeout_secs']
    expected = {(r, p, v) for r in range(repeats) for p in paths for v in variants}
    by_key = {}
    for row in rows:
        key = (row['repeat'], row['path'], row['variant'])
        if key not in expected or key in by_key:
            raise ValueError('Unexpected or duplicate paired result')
        by_key[key] = row
    if set(by_key) != expected:
        raise ValueError('Incomplete paired cohort')
    times = {k: completed_times(row, target, budget) for k, row in by_key.items()}
    pairs = [(r, p) for r in range(repeats) for p in paths]
    totals = {}
    for v in variants:
        counts = [len(times[r, p, v]) for r, p in pairs]
        totals[v] = dict(cases=len(pairs), completed_cases=sum(n == target for n in counts),
            total_completed_depths=sum(counts), possible_completed_depths=len(pairs) * target,
            statuses=dict(Counter(status(by_key[r, p, v]) for r, p in pairs)),
            reached_depth_counts={str(d): sum(n > d for n in counts) for d in range(target)})
    comparisons = []
    for left, right in itertools.combinations(variants, 2):
        all_counts, joint_counts = Counter(), Counter()
        left_only, right_only = [], []
        for r, p in pairs:
            a, b = len(times[r, p, left]), len(times[r, p, right])
            outcome = 'left_deeper' if a > b else 'right_deeper' if a < b else 'same_depth'
            all_counts[outcome] += 1
            if a < target and b < target:
                joint_counts[outcome] += 1
            if a == target and b < target:
                left_only.append(dict(repeat=r, path=p))
            if b == target and a < target:
                right_only.append(dict(repeat=r, path=p))
        comparisons.append(dict(left=left, right=right, all_cases=dict(all_counts),
            neither_completed_target=dict(joint_counts), left_only_completed=left_only,
            right_only_completed=right_only))
    flat = []
    for r, p in pairs:
        item = dict(benchmark=Path(p).name.removesuffix('.encoding.vmt'), path=p, repeat=r)
        for v in variants:
            ts, row = times[r, p, v], by_key[r, p, v]
            item.update({f'{v}_status': status(row), f'{v}_elapsed_secs': row['elapsed_secs'],
                f'{v}_completed_depths': len(ts), f'{v}_deepest_completed_depth': len(ts)-1 if ts else None,
                f'{v}_last_completion_secs': ts[-1] if ts else None,
                f'{v}_completed_target_within_budget': len(ts) == target})
        flat.append(item)
    checkpoints = sorted({t for t in (1, 5, 10, 30, 60, 120, 300, budget) if t <= budget})
    time_coverage = [dict(seconds=t, **{v: sum(sum(x <= t for x in times[r, p, v]) for r, p in pairs)
                                       for v in variants}) for t in checkpoints]
    return dict(method=dict(target_depth_count=target, checked_depths=f'0-{target-1}',
        wall_budget_secs=budget, paired_cases=len(pairs), repetitions=repeats,
        meaning='Count recorded completed depths within the wall budget; a started depth earns no credit. No unbounded proof claim.'),
        variants=totals, pairwise=comparisons, time_coverage=time_coverage, cases=flat)


def write_report(root):
    metadata = json.loads((root / 'metadata.json').read_text())
    rows = [json.loads(s) for s in (root / 'results.jsonl').read_text().splitlines()]
    report = compare(metadata, rows)
    (root / 'depth-comparison.json').write_text(json.dumps(report, indent=2) + '\n')
    with (root / 'completed-depths.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(report['cases'][0]))
        writer.writeheader()
        writer.writerows(report['cases'])
    with (root / 'depth-coverage.csv').open('w', newline='') as f:
        variants = metadata['variant_order']
        writer = csv.DictWriter(f, fieldnames=['completed_depths', *variants])
        writer.writeheader()
        writer.writerows(dict(completed_depths=d+1, **{v: report['variants'][v]['reached_depth_counts'][str(d)]
            for v in variants}) for d in range(metadata['depth']))
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('run_directory', type=Path)
    args = parser.parse_args()
    report = write_report(args.run_directory)
    print(json.dumps({k: v for k, v in report.items() if k not in ('cases', 'time_coverage')}, indent=2))
