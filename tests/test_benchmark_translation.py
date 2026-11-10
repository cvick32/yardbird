"""Semantic regressions for offline importers, checked with independent Z3 queries."""

from pathlib import Path
import unittest
import z3

from tools.benchmark_translation import cubicle, ivy, ivy_vmt, mcmt, mypyvy
from tools.benchmark_translation.core import Unsupported, sexpr, safe, subst


ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / 'examples' / 'quantified-transition-systems'


def check(model, formulas, extras=(), declarations=()):
    script = '\n'.join(sexpr(d) for d in model.declarations())
    script += '\n' + '\n'.join(declarations)
    script += '\n' + '\n'.join(sexpr(['assert', f]) for f in formulas)
    script += '\n' + '\n'.join('(assert ' + f + ')' for f in extras)
    solver = z3.Solver()
    solver.set(timeout=5000)
    solver.add(z3.parse_smt2_string(script))
    return solver.check()


class MypyvyTests(unittest.TestCase):
    def test_frames_and_derived_next_state(self):
        model = mypyvy.convert('''
sort node
mutable relation p(node)
mutable relation untouched(node)
derived relation d(node): forall X:node. d(X) <-> p(X)
init forall X:node. !p(X)
safety forall X:node. !d(X)
transition insert(x:node)
 modifies p
 forall X:node. new(p(X)) <-> (p(X) | X = x)
''')
        init, trans, prop = model.formulas()
        self.assertEqual(check(model, [init, trans]), z3.sat)
        self.assertEqual(check(model, [init, trans, model.shift(prop)]), z3.unsat)
        self.assertEqual(check(model, [trans], ['(not (= s_untouched s_untouched_next))']), z3.unsat)

    def test_missing_property_fails(self):
        model = mypyvy.convert('mutable relation p\ninit !p\ntransition go() modifies p new(p)')
        with self.assertRaises(Unsupported):
            model.render('test', 'hash')

    def test_uppercase_closure_and_shadowing(self):
        model = mypyvy.convert('''
sort node
mutable relation p(node)
init p(X)
safety forall X:node. p(X)
transition noop() = true
''')
        init, _, prop = model.formulas()
        self.assertEqual(check(model, [init, ['not', prop]]), z3.unsat)


class CubicleTests(unittest.TestCase):
    def test_fractional_real_is_not_integer_division(self):
        m = cubicle.convert('var X : real init { X = 0.5 } unsafe { X = 0.0 } transition stay () {}')
        init, _, prop = m.formulas()
        self.assertEqual(check(m, [init]), z3.sat)
        self.assertEqual(check(m, [init, ['not', prop]]), z3.unsat)
        self.assertIn('(to_real 5)', m.render('test', 'hash'))

    def test_simultaneous_and_unconditional_last_case(self):
        m = cubicle.convert('''
var X : int
var Y : int
init { X = 1 && Y = 2 }
unsafe { X = 9 }
transition swap () { X := Y; Y := case | X = 8 : 9 | X = 7 : X }
''')
        init, trans, _ = m.formulas()
        self.assertEqual(check(m, [init, trans], ['(= s_X_next 2)', '(= s_Y_next 1)']), z3.sat)
        self.assertEqual(check(m, [init, trans], ['(not (= s_Y_next 1))']), z3.unsat)

    def test_distinct_parameters(self):
        m = cubicle.convert('''
var X : int
init { X = 0 }
unsafe { X = 1 }
transition go (a b) { X := 1 }
''')
        _, trans, _ = m.formulas()
        singleton = ['(forall ((p Proc)) (= p only))']
        self.assertEqual(check(m, [trans], singleton, ['(declare-fun only () Proc)']), z3.unsat)

    def test_forall_other_excludes_all_parameters(self):
        m = cubicle.convert('''
array A[proc] : bool
init (p) { A[p] = False }
unsafe { False }
transition go (a b)
 requires { forall_other j. A[j] = True }
 { A[a] := True }
''')
        init, trans, _ = m.formulas()
        domain = ['(not (= a b))', '(forall ((p Proc)) (or (= p a) (= p b)))']
        decls = ['(declare-fun a () Proc)', '(declare-fun b () Proc)']
        self.assertEqual(check(m, [init, trans], domain, decls), z3.sat)

    def test_stored_process_outside_selected_domain(self):
        m = cubicle.convert('''
var Home : proc
array Owner[proc] : proc
init (p) { Home <> p && Owner[p] = Home }
unsafe (p) { Owner[p] <> Home }
transition stay () { }
''')
        init, trans, _ = m.formulas()
        self.assertEqual(check(m, [init, trans]), z3.sat)

    def test_enum_exhaustive_and_nondeterminism(self):
        m = cubicle.convert('''
type color = Red | Blue
var X : color
var Y : int
init { X = Red && Y = 3 }
unsafe { Y = 0 }
transition choose () { X := ? }
''')
        init, trans, _ = m.formulas()
        self.assertEqual(check(m, [init, trans], ['(= s_X_next s_Blue)']), z3.sat)
        self.assertEqual(check(m, [init, trans], ['(not (= s_Y_next 3))']), z3.unsat)
        self.assertEqual(check(m, [init, trans], ['(not (= s_X_next s_Red))', '(not (= s_X_next s_Blue))']), z3.unsat)


class MCMTTests(unittest.TestCase):
    def test_first_case_ignores_guard_and_global_is_scalar(self):
        m = mcmt.convert('''
:local a int
:global g int
:initial
:var j
:cnj (= a[j] 0) (= g[j] 4)
:unsafe
:var j
:cnj (= a[j] 2)
:transition
:var x
:var j
:guard
:numcases 2
:case false
:val 1
:val 5
:case
:val a[j]
:val 5
''')
        init, trans, _ = m.formulas()
        self.assertEqual(check(m, [init, trans]), z3.sat)
        self.assertEqual(check(m, [init, trans], ['(not (= s_g_next 5))']), z3.unsat)
        self.assertEqual(check(m, [init, trans], ['(forall ((p Proc)) (= (select s_a_next p) 0))']), z3.unsat)

    def test_uncovered_cases_are_havoc_not_frames(self):
        m = mcmt.convert('''
:local a int
:initial
:var j
:cnj (= a[j] 0)
:unsafe
:var j
:cnj (= a[j] 1)
:transition
:var j
:guard
:numcases 1
:case false
:val 9
''')
        init, trans, _ = m.formulas()
        self.assertEqual(check(m, [init, trans], ['(forall ((p Proc)) (= (select s_a_next p) 1))']), z3.sat)

    def test_parameter_aliasing_and_disjunctive_uguards(self):
        m = mcmt.convert('''
:local a int
:initial
:var j
:cnj (= a[j] 0)
:unsafe
:var x
:var y
:cnj (= a[x] 1) (= a[y] 1)
:transition
:var x
:var y
:var j
:guard (= x y)
:uguard false
:uguard true
:numcases 1
:case
:val 1
''')
        init, trans, _ = m.formulas()
        self.assertEqual(check(m, [init, trans]), z3.sat)

    def test_semantic_comment_range_has_nonempty_initial_state(self):
        m = mcmt.convert('''
:comment index_arrays ptr
:comment index_arrays_extra ptr -1
:local ptr int
:initial
:var j
:cnj (= ptr[j] -1)
:unsafe
:var j
:cnj (= ptr[j] -2)
:transition
:var j
:guard
:numcases 1
:case
:val ptr[j]
''')
        init, _, _ = m.formulas()
        self.assertEqual(check(m, [init]), z3.sat)
        self.assertEqual(check(m, [init], ['(exists ((p Proc)) (< (select s__5f__5f_index_5f_rank p) 0))']), z3.unsat)


class IvyTests(unittest.TestCase):
    def test_per_step_auxiliary_and_omitted_frame(self):
        m = ivy_vmt.convert('''
(declare-fun __p () Bool)
(declare-fun p () Bool)
(declare-fun __q () Bool)
(declare-fun q () Bool)
(declare-fun temp () Bool)
(define-fun .p () Bool (! __p :next p))
(define-fun .q () Bool (! __q :next q))
(define-fun .init () Bool (! (and (not __p) __q) :init true))
(define-fun .prop () Bool (! __q :invar-property 0))
(define-fun .a () Bool (! (and (= temp __p) (= p (not temp))) :action flip))
''')
        init, trans, _ = m.formulas()
        self.assertEqual(check(m, [init, trans]), z3.sat)
        self.assertEqual(check(m, [init, trans], ['(not s__5f__5f_q_next)']), z3.unsat)
        mapping, declarations = {}, []
        for n, s in m.symbols.items():
            mapping[safe(n)] = safe(n) + '_next'
            mapping[safe(n) + '_next'] = safe(n) + '_step2'
            declarations.append(sexpr(['declare-fun', safe(n) + '_step2', [], s.sort]))
        self.assertEqual(check(m, [init, trans, subst(trans, mapping)], declarations=declarations), z3.sat)

    def test_multisig_slice_update_and_uninitialized_expired(self):
        m = ivy.convert((CORPUS / 'ivybench/multisig/ivy/multisig-all_simple.ivy').read_text())
        init, _, _ = m.formulas()
        self.assertEqual(check(m, [init], ['(forall ((d s_deadline)) (select s_expired d))']), z3.sat)
        self.assertEqual(check(m, [init], ['(forall ((d s_deadline)) (not (select s_expired d)))']), z3.sat)
        # Under all-false expired, cancel cannot run; expire can change expired.
        cancel = dict(m.actions)['cancel']
        expire = dict(m.actions)['expire']
        all_false = '(forall ((d s_deadline)) (not (select s_expired d)))'
        self.assertEqual(check(m, [cancel], [all_false]), z3.unsat)
        self.assertEqual(check(m, [expire], [all_false]), z3.sat)
        propose = dict(m.actions)['propose']
        self.assertEqual(propose[0], 'exists')
        params = [v for v, _ in propose[1]]
        decls = [sexpr(['declare-fun', v, [], ty]) for v, ty in propose[1]]
        decls += ['(declare-fun another () s_destination)', '(declare-fun sig0 () s_signature)']
        k, v, d = params
        target = m.ref('sig', [k, v, d, 'sig0'], 1)
        self.assertEqual(check(m, [propose[2], target], declarations=decls), z3.unsat)
        before = m.ref('sig', ['another', v, d, 'sig0'])
        after = m.ref('sig', ['another', v, d, 'sig0'], 1)
        self.assertEqual(check(m, [propose[2], ['not', ['=', before, after]]],
                               [f'(not (= another {k}))'], decls), z3.unsat)


if __name__ == '__main__':
    unittest.main()
