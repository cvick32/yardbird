"""Bounded Yardbird checks of generated files; never runs imported scripts."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess
import time


def main():
    repo = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, default=repo / 'target/release/yardbird')
    parser.add_argument('--output', type=Path, default=repo / 'benchmark_results/investigations/offline-import-smoke')
    parser.add_argument('--all-parse', action='store_true', help='depth zero parser/setup smoke for every output')
    parser.add_argument('--initial-states', action='store_true', help='check nonempty initialization with Z3, 300ms per model')
    args = parser.parse_args()
    root = repo / 'examples/quantified-transition-systems/generated-vmt'
    if args.initial_states:
        import z3
        from . import cubicle, ivy, ivy_vmt, mcmt, mypyvy
        from .core import sexpr, sha256
        converters = {'cubicle': cubicle.convert, 'mypyvy': mypyvy.convert,
                      'ivy-action-vmt': ivy_vmt.convert, 'ivy-multisig': ivy.convert,
                      'mcmt-lambda-profile': mcmt.convert}
        entries = json.loads((root / 'manifest.json').read_text())['entries']
        results = []
        for entry in entries:
            if entry['status'] != 'generated':
                continue
            original = (root.parent / entry['source']).read_bytes()
            if sha256(original) != entry['source_sha256']:
                raise RuntimeError('source hash mismatch: ' + entry['source'])
            model = converters[entry['frontend']](original.decode())
            script = '\n'.join(map(sexpr, model.declarations())) + '\n' + sexpr(['assert', model.formulas()[0]])
            solver = z3.Solver()
            solver.set(timeout=300)
            solver.add(z3.parse_smt2_string(script))
            started = time.monotonic()
            status = str(solver.check())
            results.append({'source':entry['source'], 'result':status,
                            'seconds':round(time.monotonic() - started, 4)})
        args.output.mkdir(parents=True, exist_ok=True)
        (args.output / 'initial-states.json').write_text(json.dumps(results, indent=2) + '\n')
        from collections import Counter
        print(json.dumps(dict(Counter(r['result'] for r in results)), sort_keys=True))
        return
    if args.all_parse:
        paths = (root / 'vmt-inputs.txt').read_text().splitlines()
        jobs = [(p, 'concrete', 0) for p in paths]
    else:
        paths = [
            'mypyvy/examples/lockserv.pyv.vmt',
            'mypyvy/examples/client_server_ae.pyv.vmt',
            'mypyvy/examples/message_passing_litmus.pyv.vmt',
            'mypyvy/examples/peterson.pyv.vmt',
            'cubicle/examples/bakery.cub.vmt',
            'cubicle/examples/german.ctc.cub.vmt',
            'cubicle/examples/peterson_two_proc.cub.vmt',
            'lambda/benchmarks/protocols/bakery.in.vmt',
            'lambda/benchmarks/protocols/chandra_buggy.in.vmt',
            'ivybench/i4/vmt/lock_server.vmt.vmt',
            'ivybench/i4/vmt/distributed_lock.vmt.vmt',
            'ivybench/multisig/ivy/multisig-all_simple.ivy.vmt',
        ]
        jobs = [(p, s, 3) for p in paths for s in ('concrete', 'abstract')]
    args.output.mkdir(parents=True, exist_ok=True)
    for p, _, _ in jobs:
        if not (root / p).is_file():
            raise FileNotFoundError(root / p)

    def run(job):
        path, strategy, depth = job
        cmd = [str(args.binary), '-f', str(root / path), '-s', strategy,
               '-d', str(depth), '--wall-timeout-secs', '5', '--json-output']
        started = time.monotonic()
        result = {'path':path, 'strategy':strategy, 'depth':depth, 'command':cmd}
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=8)
        except subprocess.TimeoutExpired:
            result['status'] = 'external-timeout'
        else:
            result['exit_code'] = proc.returncode
            try:
                data = json.loads(proc.stdout)
            except (ValueError, TypeError):
                result.update(status='error', diagnostic=(proc.stderr or proc.stdout)[-3000:])
            else:
                result.update(status=data.get('run_progress', {}).get('termination_reason', 'unknown'),
                              progress=data.get('run_progress'), counterexample=data.get('counterexample'),
                              found_proof=data.get('found_proof'), instances=data.get('total_instantiations_added'))
        result['elapsed_secs'] = round(time.monotonic() - started, 3)
        return result

    with ThreadPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(run, jobs))
    filename = 'parse-results.json' if args.all_parse else 'bmc-results.json'
    (args.output / filename).write_text(json.dumps(results, indent=2) + '\n')
    from collections import Counter
    print(json.dumps(dict(Counter(r['status'] for r in results)), sort_keys=True))
    for result in results:
        if result['status'] == 'error':
            print(result['path'], result.get('diagnostic'))


if __name__ == '__main__':
    main()
