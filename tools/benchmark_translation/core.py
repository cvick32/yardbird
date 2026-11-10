"""Small explicit transition-system IR and deterministic VMT writer.

Every function is represented by a scalar nested array. Even rigid symbols have
a current/next pair: Yardbird otherwise treats unpaired scalar declarations as
inputs. Frontends supply action frames; this writer only frames rigid symbols.
"""

from dataclasses import dataclass, field
import hashlib
from scripts.encode_distributed_protocols import pretty


class Unsupported(ValueError):
    pass


def sexpr(t):
    return '(' + ' '.join(map(sexpr, t)) + ')' if isinstance(t, list) else str(t)


def both(xs):
    xs = [x for x in xs if x != 'true']
    return 'true' if not xs else xs[0] if len(xs) == 1 else ['and', *xs]


def either(xs):
    xs = [x for x in xs if x != 'false']
    return 'false' if not xs else xs[0] if len(xs) == 1 else ['or', *xs]


def neg(t):
    return ['not', t]


def distinct(xs):
    return both([neg(['=', a, b]) for i, a in enumerate(xs) for b in xs[i + 1:]])


def quant(kind, bindings, body):
    return [kind, bindings, body] if bindings else body


def safe(name):
    # Injective, readable and independent of SMT reserved words.
    return 's_' + ''.join(c if c.isascii() and c.isalnum() else f'_{ord(c):x}_' for c in name)


def read(name, args):
    for arg in args:
        name = ['select', name, arg]
    return name


def subst(t, env):
    """Substitute globally fresh names. Binder shadowing is preserved."""
    if isinstance(t, str):
        return env.get(t, t)
    if t and t[0] in ('forall', 'exists'):
        local = {k: v for k, v in env.items() if k not in [b[0] for b in t[1]]}
        return [t[0], t[1], subst(t[2], local)]
    return [subst(x, env) for x in t]


@dataclass
class Symbol:
    name: str
    args: list
    result: str
    rigid: bool = False

    @property
    def sort(self):
        result = self.result
        for s in reversed(self.args):
            result = ['Array', s, result]
        return result


@dataclass
class Model:
    sorts: list = field(default_factory=list)
    symbols: dict = field(default_factory=dict)
    init: list = field(default_factory=list)
    actions: list = field(default_factory=list)
    properties: list = field(default_factory=list)
    axioms: list = field(default_factory=list)
    notes: list = field(default_factory=list)

    def add(self, name, args, result, rigid=False):
        if name in self.symbols:
            raise Unsupported(f'duplicate symbol {name}')
        self.symbols[name] = Symbol(name, args, result, rigid)

    def ref(self, name, args=(), state=0):
        s = self.symbols[name]
        if state not in (0, 1):
            raise Unsupported(f'reference to state {state}')
        return read(safe(name) + ('_next' if state and not s.rigid else ''), args)

    def frame(self, name):
        return ['=', safe(name) + '_next', safe(name)]

    def shift(self, t):
        return subst(t, {safe(n): safe(n) + '_next' for n, s in self.symbols.items() if not s.rigid})

    def formulas(self):
        if not self.properties:
            raise Unsupported('no safety property (trace-only models are not converted)')
        frozen = [self.frame(n) for n, s in self.symbols.items() if s.rigid]
        return (both([*self.init, *self.axioms]),
                both([either([body for _, body in self.actions]), *frozen,
                      *self.axioms, *[self.shift(a) for a in self.axioms]]),
                both(self.properties))

    def declarations(self):
        out = [['declare-sort', s, '0'] for s in self.sorts]
        for n, s in self.symbols.items():
            out.extend([['declare-fun', safe(n), [], s.sort],
                        ['declare-fun', safe(n) + '_next', [], s.sort]])
        return out

    def render(self, source, digest):
        init, trans, prop = self.formulas()
        out = [f'; Generated offline from {source}', f'; Source SHA-256: {digest}',
               '; Regenerate: python -m tools.benchmark_translation',
               '; Function/relation state is encoded as nested arrays.']
        out.extend('; ' + n.replace('\n', ' ') for n in self.notes)
        out.extend(map(sexpr, self.declarations()))
        for i, (n, s) in enumerate(self.symbols.items()):
            out.append(f'; source symbol: {n}')
            out.append(sexpr(['define-fun', f'link_{i}', [], s.sort,
                              ['!', safe(n), ':next', safe(n) + '_next']]))
        for i, (name, body) in enumerate(self.actions):
            out.append('; action: ' + name)
            out.append(pretty(['define-fun', f'action_{i}', [], 'Bool', body]))
        # Keep action definitions as readable, zero-arity helpers.
        action_terms = [f'action_{i}' for i in range(len(self.actions))]
        if self.actions:
            raw = either([b for _, b in self.actions])
            if trans == raw:
                trans = either(action_terms)
            elif isinstance(trans, list) and trans[0] == 'and' and trans[1] == raw:
                trans = ['and', either(action_terms), *trans[2:]]
        for name, term, attr in [('init', init, ':init'), ('trans', trans, ':trans'),
                                 ('property', prop, ':invar-property')]:
            out.append(pretty(['define-fun', name, [], 'Bool', ['!', term, attr, '0' if attr == ':invar-property' else 'true']]))
        return '\n'.join(out) + '\n'

    def validate(self):
        """Type-check complete formulas with an independent SMT-LIB reader."""
        import z3
        text = '\n'.join(map(sexpr, self.declarations()))
        text += '\n' + '\n'.join(sexpr(['assert', f]) for f in self.formulas())
        z3.parse_smt2_string(text)


def sha256(data):
    return hashlib.sha256(data).hexdigest()
