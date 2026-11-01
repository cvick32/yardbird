"""Strict Ivy subset used by the four imported multisig examples.

Elaborate to current mypyvy, using its sort inference and binder handling.
Only Boolean assignments to distinct relations with guards before updates are
accepted. This is deliberately not a general Ivy compiler.
"""

import re
from .core import Unsupported
from . import mypyvy


def elaborate(text):
    text = re.sub(r'#[^\n]*', '', text)
    lines = [l.strip() for l in text.splitlines() if l.strip()]
    relations, types, axioms, invariants, actions, exports = {}, [], [], [], {}, []
    initial = None
    i = 0
    while i < len(lines):
        line = lines[i]
        i += 1
        if line.startswith('type '):
            types.append(line[5:])
        elif line.startswith('relation '):
            match = re.fullmatch(r'relation (\w+)(?:\(([^)]*)\))?(?:\s*=\s*(.*))?', line)
            if not match:
                raise Unsupported('unsupported Ivy relation declaration')
            name, params, definition = match.groups()
            args = [tuple(a.strip().split(':')) for a in params.split(',')] if params else []
            if any(len(a) != 2 for a in args):
                raise Unsupported('Ivy declaration requires typed arguments')
            relations[name] = (args, definition)
        elif line.startswith('axiom '):
            axioms.append(line[6:])
        elif line.startswith('invariant '):
            invariants.append(line[10:])
        elif line.startswith('export '):
            exports.append(line[7:])
        elif line.startswith(('action ', 'after init')):
            if not line.endswith('{'):
                raise Unsupported('Ivy block must open on header line')
            body = []
            while i < len(lines) and lines[i] != '}':
                body.append(lines[i])
                i += 1
            if i == len(lines):
                raise Unsupported('unterminated Ivy block')
            i += 1
            body = ' '.join(body)
            if line.startswith('after init'):
                if initial is not None:
                    raise Unsupported('multiple initialization blocks')
                initial = body
            else:
                match = re.fullmatch(r'action (\w+)\(([^)]*)\)\s*=\s*\{', line)
                if not match:
                    raise Unsupported('unsupported Ivy action declaration')
                name, params = match.groups()
                actions[name] = (params, body)
        else:
            raise Unsupported(f'unsupported Ivy statement: {line}')

    def statements(body):
        guards, writes = [], {}
        for stmt in body.split(';'):
            stmt = stmt.strip()
            if not stmt:
                continue
            if stmt.startswith('require '):
                if writes:
                    raise Unsupported('require after assignment needs sequential elaboration')
                guards.append(stmt[8:])
                continue
            match = re.fullmatch(r'(\w+)(?:\(([^)]*)\))?\s*:=\s*(true|false)', stmt)
            if not match:
                raise Unsupported(f'unsupported Ivy update: {stmt}')
            name, args, val = match.groups()
            if name in writes:
                raise Unsupported('repeated assignment needs sequential elaboration')
            writes[name] = ([a.strip() for a in args.split(',')] if args else [], val)
        return guards, writes

    if initial is None:
        raise Unsupported('missing Ivy initialization')
    init_guards, init_writes = statements(initial)
    if init_guards:
        raise Unsupported('guards in Ivy initialization')
    parsed = {n: (params, *statements(body)) for n, (params, body) in actions.items()}
    mutable = set(init_writes)
    for _, _, writes in parsed.values():
        mutable.update(writes)
    out = ['sort ' + ty for ty in types]
    for name, (args, definition) in relations.items():
        sig = name + '(' + ', '.join(ty for _, ty in args) + ')' if args else name
        if definition:
            call = name + '(' + ', '.join(n for n, _ in args) + ')'
            bs = ', '.join(n + ':' + ty for n, ty in args)
            out.append(f'derived relation {sig}: forall {bs}. {call} <-> ({definition})')
        else:
            out.append(('mutable' if name in mutable else 'immutable') + ' relation ' + sig)
    out.extend('axiom ' + a for a in axioms)
    for name, (targets, val) in init_writes.items():
        args, _ = relations[name]
        if len(args) != len(targets) or any(not t.isupper() for t in targets) or len(targets) != len(set(targets)):
            raise Unsupported('initialization must cover entire relation')
        call = name + '(' + ', '.join(targets) + ')' if args else name
        out.append('init ' + call + ' = ' + val)
    if set(exports) != set(actions):
        raise Unsupported('subset exporter requires all actions exported exactly once')
    for name in exports:
        params, guards, writes = parsed[name]
        terms = list(guards)
        for relation, (targets, val) in writes.items():
            args, definition = relations[relation]
            if definition or len(targets) != len(args):
                raise Unsupported('invalid relation update')
            if len([x for x in targets if x.isupper()]) != len(set(x for x in targets if x.isupper())):
                raise Unsupported('repeated slice binder')
            binders = [(f'update_{k}', ty) for k, (_, ty) in enumerate(args)]
            call = relation + '(' + ', '.join(v for v, _ in binders) + ')' if args else relation
            conditions = [f'{v} = {target}' for (v, _), target in zip(binders, targets) if not target.isupper()]
            cond = ' & '.join(conditions) or 'true'
            body = f"new({call}) = (if {cond} then {val} else {call})"
            if binders:
                body = 'forall ' + ', '.join(v + ':' + ty for v, ty in binders) + '. ' + body
            terms.append(body)
        out.append(f'transition {name}({params}) modifies ' + ', '.join(writes) + '\n' + ' &\n'.join('(' + t + ')' for t in terms))
    out.extend('safety ' + inv for inv in invariants)
    return '\n'.join(out)


def convert(text, filename='<ivy>'):
    m = mypyvy.convert(elaborate(text), filename)
    m.notes.append('Ivy multisig subset: Boolean point/slice updates; missing initializers remain unconstrained.')
    return m
