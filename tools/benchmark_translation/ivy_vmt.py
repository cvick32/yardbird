"""Normalize the pinned IC3PO action VMT dialect without altering originals."""

from scripts.encode_distributed_protocols import parse_spans
from .core import Model, Unsupported, both, distinct, safe


def convert(text):
    commands = [t for t, _, _ in parse_spans(text)]
    m = Model()
    decls, pairs, globals_, definitions = {}, {}, set(), {}
    tagged = []
    for c in commands:
        if c[0] == 'declare-sort':
            if c[2] != '0':
                raise Unsupported('parameterized sort')
            m.sorts.append(safe(c[1]))
        elif c[0] == 'declare-fun':
            decls[c[1]] = (c[2], c[3])
        elif c[0] == 'declare-const':
            decls[c[1]] = ([], c[2])
        elif c[0] == 'define-fun':
            body = c[4]
            if isinstance(body, list) and body[0] == '!':
                attrs = dict(zip(body[2::2], body[3::2]))
                tagged.append((attrs, body[1]))
                if ':next' in attrs:
                    cur = body[1][0] if isinstance(body[1], list) else body[1]
                    pairs[cur] = attrs[':next']
                if ':global' in attrs:
                    globals_.add(body[1][0] if isinstance(body[1], list) else body[1])
            else:
                definitions[c[1]] = (c[2], body)
        elif c[0] not in ('set-logic', 'set-info', 'set-option'):
            raise Unsupported(f'Ivy VMT command {c[0]}')

    def sort(t):
        if isinstance(t, list):
            return [t[0], *[sort(x) for x in t[1:]]]
        return t if t in ('Bool', 'Int', 'Real') or t.isdigit() else safe(t)

    back = {n: c for c, n in pairs.items()}
    for name, (args, result) in decls.items():
        if name not in back:
            m.add(name, list(map(sort, args)), sort(result), name in globals_)
    serial = 0

    def lower(t, env=None, active=()):
        nonlocal serial
        env = {} if env is None else env
        if isinstance(t, str):
            if t in env:
                return env[t]
            if t in decls:
                return m.ref(back.get(t, t), state=int(t in back))
            if t in definitions:
                if t in active:
                    raise Unsupported('recursive definition')
                return lower(definitions[t][1], env, (*active, t))
            return t
        op = t[0]
        if op == '!':
            return lower(t[1], env, active)
        if op == 'let':
            additions = {n: lower(v, env, active) for n, v in t[1]}
            return lower(t[2], {**env, **additions}, active)
        if op in ('forall', 'exists'):
            bs, inner = [], dict(env)
            for n, ty in t[1]:
                serial += 1
                inner[n] = f'q_{serial}_{safe(n)}'
                bs.append([inner[n], sort(ty)])
            return [op, bs, lower(t[2], inner, active)]
        args = [lower(a, env, active) for a in t[1:]]
        if op in decls:
            return m.ref(back.get(op, op), args, int(op in back))
        if op in definitions:
            if op in active:
                raise Unsupported('recursive definition')
            params, body = definitions[op]
            return lower(body, {**env, **{b[0]: a for b, a in zip(params, args)}}, (*active, op))
        if op == 'distinct':
            return distinct(args)
        return [op, *args]

    # Metadata names the predicate whose defining equivalence follows.
    derived = set()
    for attrs, body in tagged:
        if ':definition' in attrs:
            target = attrs[':definition']
            derived.add(back.get(target, target))
    for attrs, body in tagged:
        if ':init' in attrs:
            m.init.append(lower(body))
        if ':invar-property' in attrs:
            m.properties.append(lower(body))
        if ':axiom' in attrs:
            m.axioms.append(lower(body))
        if ':definition' in attrs:
            # Source emits both state versions; the writer supplies the next copy.
            if attrs[':definition'] not in back:
                m.axioms.append(lower(body))
        if ':action' in attrs:
            result = lower(body)
            used = set()
            def visit(t):
                if isinstance(t, str):
                    used.add(t)
                else:
                    for x in t:
                        visit(x)
            visit(result)
            frames = [m.frame(n) for n in pairs if n not in derived and safe(n) + '_next' not in used]
            m.actions.append((attrs[':action'], both([result, *frames])))
    if not m.init or not m.actions:
        raise Unsupported('missing initial condition or actions')
    m.notes.extend(['Normalized IC3PO :action dialect; omitted state symbols framed per action.',
                    'Unpaired non-global auxiliaries are unconstrained per-frame inputs.',
                    ':sort cardinalities are finite-instance hints, not domain axioms.'])
    return m
