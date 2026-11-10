import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('depths', Path(__file__).resolve().parents[1] / 'compare_quantified_depths.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


def row(v, times, status='external_timeout', **progress):
    return dict(path='/a.encoding.vmt', repeat=0, variant=v, status=status,
        elapsed_secs=500, counterexample=False, progress=dict(depth_completions=[
            dict(depth=d, elapsed_wall_secs=t) for d, t in enumerate(times)],
            deepest_completed_depth=len(times)-1 if times else None, **progress))


class DepthComparison(unittest.TestCase):
    def setUp(self):
        self.meta = dict(variant_order=['fixed', 'guided', 'z3'], input_order=['/a.encoding.vmt'],
                         repeat=1, depth=20, timeout_secs=500)

    def test_partial_progress_and_unknown_are_counted_without_started_depth(self):
        rows = [row('fixed', [1, 2, 3], current_depth=3), row('guided', [1, 4]),
                row('z3', [1], 'error', termination_reason='solver_unknown', current_depth=19)]
        report = m.compare(self.meta, rows)
        self.assertEqual(report['variants']['fixed']['total_completed_depths'], 3)
        self.assertEqual(report['variants']['z3']['total_completed_depths'], 1)
        self.assertEqual(report['variants']['z3']['statuses'], {'unknown': 1})
        self.assertEqual(report['pairwise'][1]['neither_completed_target'], {'left_deeper': 1})
        self.assertEqual(report['variants']['fixed']['reached_depth_counts']['3'], 0)

    def test_depth_zero_counts_as_one_and_no_progress_as_zero(self):
        report = m.compare(self.meta, [row('fixed', [0.1]), row('guided', []), row('z3', [])])
        self.assertEqual(report['cases'][0]['fixed_completed_depths'], 1)
        self.assertIsNone(report['cases'][0]['z3_deepest_completed_depth'])
        self.assertEqual(report['pairwise'][2]['all_cases'], {'same_depth': 1})

    def test_deadline_excludes_late_completions(self):
        report = m.compare(self.meta, [row('fixed', [1, 500, 500.01]), row('guided', []), row('z3', [])])
        self.assertEqual(report['variants']['fixed']['total_completed_depths'], 2)
        self.assertEqual(report['time_coverage'][-1]['fixed'], 2)

    def test_completed_target_and_pairwise_cohorts(self):
        report = m.compare(self.meta, [row('fixed', range(20), 'depth_limit'),
            row('guided', range(20), 'depth_limit'), row('z3', range(19))])
        self.assertEqual(report['variants']['fixed']['completed_cases'], 1)
        self.assertEqual(report['variants']['fixed']['total_completed_depths'], 20)
        self.assertEqual(report['pairwise'][1]['neither_completed_target'], {})
        self.assertEqual(len(report['pairwise'][1]['left_only_completed']), 1)

    def test_invalid_and_incomplete_records_rejected(self):
        rows = [row(v, [1, 2]) for v in self.meta['variant_order']]
        for bad in [rows[:-1], rows + [rows[0]]]:
            with self.assertRaises(ValueError): m.compare(self.meta, bad)
        rows[0]['progress']['depth_completions'][1]['depth'] = 0
        with self.assertRaises(ValueError): m.compare(self.meta, rows)
        with self.assertRaises(ValueError): m.completed_times(row('fixed', [2, 1]), 20, 500)
        with self.assertRaises(ValueError): m.completed_times(row('fixed', [1], 'depth_limit'), 20, 500)


if __name__ == '__main__': unittest.main()
