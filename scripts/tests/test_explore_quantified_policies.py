"""Checkpoint and completion-contract tests; no solver or network required."""
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

REPO = Path(__file__).resolve().parents[2]
RUNNER = REPO / "scripts/explore_quantified_policies.py"


class Checkpoints(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.binary = self.root / "solver"
        self.binary.write_text(f"#!{sys.executable}\n" + r'''
import json, os, sys
from pathlib import Path
args = sys.argv
n = int(args[args.index('-d') + 1])
log = Path(__file__).with_name('calls')
with log.open('a') as f: f.write('called\n')
depths = list(range(n))
if os.environ.get('MOCK_BAD_PROGRESS'): depths = [0] * n
progress = dict(termination_reason='depth_limit', deepest_completed_depth=n-1,
    depth_completions=[dict(depth=d, elapsed_wall_secs=0.01) for d in depths])
Path(args[args.index('--progress-file')+1]).write_text(json.dumps(progress))
print(json.dumps(dict(run_progress=progress, counterexample=False, found_proof=False)))
''')
        self.binary.chmod(0o755)
        model = self.root / "model.vmt"
        model.write_text("; mock input\n")
        self.inputs = self.root / "inputs.txt"
        self.inputs.write_text(str(model) + "\n")
        self.output = self.root / "results"

    def run_tool(self, *extra, env=None):
        return subprocess.run([sys.executable, str(RUNNER), '--binary', str(self.binary),
            '--inputs', str(self.inputs), '--variants', 'guided4096-split-properties', 'z3-assuming',
            '--depth', '2', '--timeout-secs', '1', '--external-grace-secs', '0',
            '--output', str(self.output), *extra], cwd=REPO, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env)

    def records(self):
        return [json.loads(s) for s in (self.output / 'results.jsonl').read_text().splitlines()]

    def test_resume_skips_completed_and_archives_interrupted_attempt(self):
        self.assertEqual(self.run_tool().returncode, 0)
        original = self.records()
        self.assertEqual(self.run_tool('--resume').returncode, 0)
        self.assertEqual(self.records(), original)
        self.assertEqual(len((self.root / 'calls').read_text().splitlines()), 2)
        (self.output / 'results.jsonl').write_text(json.dumps(original[0]) + '\n')
        self.assertEqual(self.run_tool('--resume').returncode, 0)
        self.assertEqual(len(self.records()), 2)
        self.assertEqual(len((self.root / 'calls').read_text().splitlines()), 3)
        self.assertTrue(list((self.output / 'interrupted').glob('*/*.progress.json')))
        self.assertEqual(json.loads((self.output / 'status.json').read_text())['completed'], 2)

    def test_resume_rejects_changed_settings_or_binary(self):
        self.assertEqual(self.run_tool().returncode, 0)
        self.assertIn('depth differs', self.run_tool('--resume', '--depth', '3').stderr)
        with self.binary.open('a') as f: f.write('\n# changed\n')
        self.assertIn('binary_sha256 differs', self.run_tool('--resume').stderr)
        self.assertEqual(len((self.root / 'calls').read_text().splitlines()), 2)

    def test_resume_rejects_duplicates_and_concurrent_runner(self):
        self.assertEqual(self.run_tool().returncode, 0)
        with (self.output / '.runner.lock').open('a') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            self.assertIn('already holds', self.run_tool('--resume').stderr)
        with (self.output / 'results.jsonl').open('a') as f:
            f.write(json.dumps(self.records()[0]) + '\n')
        self.assertIn('duplicate checkpoint', self.run_tool('--resume').stderr)

    def test_resume_rejects_reordered_inputs_and_variants(self):
        second = self.root / 'other.vmt'
        second.write_text('; second mock input\n')
        original = self.inputs.read_text()
        self.inputs.write_text(original + str(second) + '\n')
        self.assertEqual(self.run_tool().returncode, 0)
        self.inputs.write_text(str(second) + '\n' + original)
        self.assertIn('input_order differs', self.run_tool('--resume').stderr)
        self.inputs.write_text(original + str(second) + '\n')
        self.assertIn('variant_order differs', self.run_tool('--resume', '--variants',
            'z3-assuming', 'guided4096-split-properties').stderr)

    def test_duplicate_depths_are_not_counted_as_completion(self):
        result = self.run_tool(env={**os.environ, 'MOCK_BAD_PROGRESS': '1'})
        self.assertEqual(result.returncode, 0)
        self.assertEqual([r['status'] for r in self.records()], ['invalid_completion'] * 2)


if __name__ == '__main__':
    unittest.main()
