"""Use the pinned upstream parser/typechecker, then emit explicit state formulas."""

import argparse
import contextlib
import io
from pathlib import Path
import sys

from .core import Model, Unsupported, both, distinct, quant, safe


def frontend():
    vendor = Path(__file__).parent / 'vendor' / 'mypyvy'
    if str(vendor) not in sys.path:
        sys.path.insert(0, str(vendor))
    import parser
    import syntax
    import typechecker
    import utils
    import ply.yacc
    utils.args = argparse.Namespace(error_filename_basename=False, exit_on_error=False, json=False)
    # No generated parse tables in the vendored tree.
    if parser.program_parser is None:
        parser.program_parser = ply.yacc.yacc(module=parser, start='program', debug=False, write_tables=False)
    return parser, syntax, typechecker, utils


def convert(text, filename='<input>'):
    parser, s, tc, utils = frontend()
    utils.error_count = 0
    diagnostics = io.StringIO()
    with contextlib.redirect_stdout(diagnostics):
        p = parser.get_parser().parse(input=text, lexer=parser.get_lexer(), filename=filename)
        if p is not None and not utils.error_count:
            tc.typecheck_program(p)
    if p is None or utils.error_count:
        raise Unsupported('upstream parser/typechecker: ' + diagnostics.getvalue().strip())
    m = Model()

    def sort(x):
        name = str(x)
        return {'bool': 'Bool', 'int': 'Int'}.get(name, safe(name))

    m.sorts = [safe(d.name) for d in p.sorts()]
    for d in p.relations_constants_and_functions():
        m.add(d.name, [sort(x) for x in getattr(d, 'arity', ())],
              'Bool' if isinstance(d, s.RelationDecl) else sort(d.sort), not d.mutable)
    serial = 0

    def emit(e, env=None, state=0):
        nonlocal serial
        env = {} if env is None else env
        if isinstance(e, s.Bool):
            return 'true' if e.val else 'false'
        if isinstance(e, s.Int):
            return str(e.val) if e.val >= 0 else ['-', str(-e.val)]
        if isinstance(e, s.UnaryExpr):
            return emit(e.arg, env, state + 1) if e.op == 'NEW' else ['not', emit(e.arg, env, state)]
        if isinstance(e, s.BinaryExpr):
            ops = dict(IMPLIES='=>', IFF='=', EQUAL='=', NOTEQ='=', GE='>=', GT='>', LE='<=', LT='<', PLUS='+', SUB='-', MULT='*')
            t = [ops[e.op], emit(e.arg1, env, state), emit(e.arg2, env, state)]
            return ['not', t] if e.op == 'NOTEQ' else t
        if isinstance(e, s.NaryExpr):
            args = [emit(x, env, state) for x in e.args]
            if e.op == 'DISTINCT':
                return distinct(args)
            if e.op == 'AND':
                return both(args)
            from .core import either
            return either(args)
        if isinstance(e, (s.Id, s.AppExpr)):
            n = e.name if isinstance(e, s.Id) else e.callee
            if n in env:
                return env[n]
            args = [] if isinstance(e, s.Id) else [emit(x, env, state) for x in e.args]
            return m.ref(n, args, state + e.n_new)
        if isinstance(e, s.QuantifierExpr):
            inner = dict(env)
            bs = []
            for v in e.binder.vs:
                serial += 1
                inner[v.name] = f'q_{serial}_{safe(v.name)}'
                bs.append([inner[v.name], sort(v.sort)])
            return quant(e.quant.lower(), bs, emit(e.body, inner, state))
        if isinstance(e, s.IfThenElse):
            return ['ite', emit(e.branch, env, state), emit(e.then, env, state), emit(e.els, env, state)]
        if isinstance(e, s.Let):
            return emit(e.body, {**env, e.binder.vs[0].name: emit(e.val, env, state)}, state)
        raise Unsupported(f'unsupported mypyvy AST: {type(e).__name__}')

    def formula(e, state=0):
        return emit(s.expand_macros(p.scope, e), state=state)

    with s.prog_context(p):
        m.init = [formula(d.expr) for d in p.inits()]
        m.axioms = [formula(d.expr) for d in p.axioms()]
        m.axioms.extend(formula(d.derived_axiom) for d in p.derived_relations())
        for d in p.transitions():
            # Upstream's `= expr` production uses [] for an empty modifies
            # clause, whereas its frame helper concatenates tuples.
            d.mods = tuple(d.mods)
            m.actions.append((d.name, formula(d.as_twostate_formula(p.scope))))
        selected = list(p.safeties())
        if not selected:
            selected = list(p.invs())
            if selected:
                m.notes.append('No safety annotation; checking all declared invariants as properties.')
        m.properties = [formula(d.expr) for d in selected]
        m.notes.append('Auxiliary strengthening invariants are not assumed. Trace/theorem commands are not transition constraints.')
    return m
