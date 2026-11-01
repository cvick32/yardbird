"""Strict Cubicle frontend for the imported grammar (no solver dependency)."""

import re
from .core import Model, Unsupported, both, either, distinct, quant, safe, neg


def tokenize(text):
    # Cubicle comments nest.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('(*', i):
            depth += 1
            i += 2
        elif depth and text.startswith('*)', i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise Unsupported('unterminated comment')
    text = ''.join(out)
    pattern = r'\s+|<=>|<->|:=|<>|!=|<=|>=|&&|\|\||=>|->|#[0-9]+|[0-9]+\.[0-9]+|[0-9]+|[A-Za-z_][A-Za-z_0-9]*|[{}()\[\],;:.?+*/=<>|\-]'
    tokens, pos = [], 0
    for match in re.finditer(pattern, text):
        if match.start() != pos:
            raise Unsupported(f'unrecognized Cubicle text: {text[pos:pos+40]!r}')
        pos = match.end()
        if not match[0].isspace():
            tokens.append(match[0])
    if pos != len(text):
        raise Unsupported('unrecognized trailing Cubicle text')
    return tokens


class Parser:
    def __init__(self, tokens):
        self.ts, self.i = tokens, 0

    def peek(self):
        return self.ts[self.i] if self.i < len(self.ts) else None

    def pop(self, expected=None):
        t = self.peek()
        if t is None or expected is not None and t != expected:
            raise Unsupported(f'expected {expected}, got {t} near {self.ts[max(0,self.i-4):self.i+7]}')
        self.i += 1
        return t

    def accept(self, t):
        if self.peek() == t:
            self.i += 1
            return True
        return False

    def group(self, left, right):
        self.pop(left)
        start, depth = self.i, 1
        while depth:
            t = self.pop()
            depth += (t == left) - (t == right)
        return self.ts[start:self.i-1]


class Cubicle:
    def __init__(self):
        self.m = Model(sorts=['Proc'])
        self.types = {'proc': 'Proc', 'int': 'Int', 'real': 'Real', 'bool': 'Bool'}
        self.macros = {}
        self.serial = 0
        self.ordered = False
        self.parameters = []

    def fresh(self, name, ty='Proc'):
        self.serial += 1
        return f'q_{self.serial}_{safe(name)}', ty

    def bindings(self, names):
        env = {n: self.fresh(n) for n in names}
        return env, [[v, ty] for v, ty in env.values()]

    def as_int(self, value, ty):
        if ty != 'Proc':
            return value
        self.ordered = True
        if '__proc_rank' not in self.m.symbols:
            self.m.add('__proc_rank', ['Proc'], 'Int', True)
        return self.m.ref('__proc_rank', [value])

    def expression(self, tokens, env):
        p = Parser(tokens)
        value = self.expr(p, env)
        if p.peek() is not None:
            raise Unsupported(f'unconsumed expression: {p.ts[p.i:]}')
        return value[0]

    def expr(self, p, env, minimum=0):
        op = p.pop()
        if op == '(':
            lhs = self.expr(p, env)
            p.pop(')')
        elif op in ('not', '-'):
            arg, ty = self.expr(p, env, 60)
            lhs = ([op, arg], 'Bool' if op == 'not' else ty)
        elif op in ('forall', 'exists', 'forall_other', 'exists_other'):
            names = [p.pop()]
            while p.accept('<>'):
                names.append(p.pop())
            p.pop('.')
            extra, bs = self.bindings(names)
            body, _ = self.expr(p, {**env, **extra})
            conditions = [distinct([v for v, _ in extra.values()])]
            if op.endswith('_other'):
                conditions.extend(neg(['=', v, env[a][0]]) for v, _ in extra.values() for a in self.parameters)
            guard = both(conditions)
            kind = op.split('_')[0]
            body = ['=>', guard, body] if kind == 'forall' else both([guard, body])
            lhs = (quant(kind, bs, body), 'Bool')
        elif op == 'if':
            condition, _ = self.expr(p, env)
            p.pop('then')
            yes, ty = self.expr(p, env)
            p.pop('else')
            no, _ = self.expr(p, env)
            lhs = (['ite', condition, yes, no], ty)
        elif op in ('True', 'False', 'true', 'false'):
            lhs = (op.lower(), 'Bool')
        elif re.fullmatch(r'\d+(?:\.\d+)?', op):
            if '.' in op:
                a, b = op.split('.')
                # Rational arithmetic avoids unsupported SMT decimal literals.
                lhs = (['/', ['to_real', str(int(a+b))], ['to_real', str(10 ** len(b))]], 'Real')
            else:
                lhs = (op, 'Int')
        elif op in self.macros and p.accept('('):
            args = []
            if not p.accept(')'):
                while True:
                    args.append(self.expr(p, env))
                    if p.accept(')'):
                        break
                    p.pop(',')
            params, body = self.macros[op]
            if len(params) != len(args):
                raise Unsupported('macro arity mismatch')
            sub = Parser(body)
            lhs = self.expr(sub, {**env, **dict(zip(params, args))})
            if sub.peek():
                raise Unsupported('macro expression not consumed')
        elif op in env:
            lhs = env[op]
        elif op in self.m.symbols:
            args = []
            if p.accept('['):
                while True:
                    a, ty = self.expr(p, env)
                    if ty != 'Proc':
                        raise Unsupported('legacy array index is not a process witness')
                    args.append(a)
                    if p.accept(']'):
                        break
                    p.pop(',')
            sym = self.m.symbols[op]
            if len(args) != len(sym.args):
                raise Unsupported(f'wrong arity for {op}')
            lhs = (self.m.ref(op, args), sym.result)
        else:
            raise Unsupported(f'unknown Cubicle term {op}')
        precedence = {'<=>':10, '<->':10, '=>':10, '->':10, '||':20, 'or':20,
                      '&&':30, 'and':30, '=':40, '<>':40, '!=':40, '<':40, '>':40,
                      '<=':40, '>=':40, '+':50, '-':50, '*':55}
        while p.peek() in precedence and precedence[p.peek()] >= minimum:
            operator = p.pop()
            rhs = self.expr(p, env, precedence[operator] + (0 if precedence[operator] <= 30 else 1))
            a, at = lhs
            b, bt = rhs
            if operator in ('<', '>', '<=', '>=', '+', '-', '*') and 'Proc' in (at, bt) or operator in ('=', '<>', '!=') and 'Proc' in (at, bt) and at != bt:
                self.ordered = True
                if '__proc_rank' not in self.m.symbols:
                    self.m.add('__proc_rank', ['Proc'], 'Int', True)
                a = self.m.ref('__proc_rank', [a]) if at == 'Proc' else a
                b = self.m.ref('__proc_rank', [b]) if bt == 'Proc' else b
            smt_op = {'&&':'and', '||':'or', '<>':'=', '!=':'=', '=>':'=>', '->':'=>', '<=>':'=', '<->':'='}.get(operator, operator)
            t = [smt_op, a, b]
            if operator in ('<>', '!='):
                t = neg(t)
            lhs = (t, at if operator in ('+', '-', '*') else 'Bool')
        return lhs

    def cases(self, p, env, result_sort):
        branches = []
        while p.accept('|'):
            cond = 'true' if p.accept('_') else self.expr(p, env)[0]
            p.pop(':')
            val, ty = self.expr(p, env)
            if result_sort == 'Int':
                val = self.as_int(val, ty)
            branches.append((cond, val))
        if not branches:
            raise Unsupported('empty case expression')
        result = branches[-1][1]
        for c, v in reversed(branches[:-1]):
            result = ['ite', c, v, result]
        return result

    def convert(self, text):
        p = Parser(tokenize(text))
        while p.peek():
            kind = p.pop()
            if kind == 'number_procs':
                count = int(p.pop())
                names = [f'#{i+1}' for i in range(count)]
                for n in names:
                    self.m.add(n, [], 'Proc', True)
                vals = [self.m.ref(n) for n in names]
                self.m.axioms += [distinct(vals), ['forall', [['enum_proc', 'Proc']], either([['=', 'enum_proc', v] for v in vals])]]
            elif kind == 'type':
                name = p.pop()
                ty = self.types[name] = safe(name)
                self.m.sorts.append(ty)
                if p.accept('='):
                    p.accept('|')
                    constructors = [p.pop()]
                    while p.accept('|'):
                        constructors.append(p.pop())
                    for c in constructors:
                        self.m.add(c, [], ty, True)
                    vals = [self.m.ref(c) for c in constructors]
                    v, _ = self.fresh('enum', ty)
                    self.m.axioms += [distinct(vals), ['forall', [[v, ty]], either([['=', v, x] for x in vals])]]
            elif kind in ('var', 'const', 'array'):
                name, args = p.pop(), []
                if kind == 'array':
                    args = [self.types[t] for t in p.group('[', ']') if t != ',']
                p.pop(':')
                result = self.types[p.pop()]
                self.m.add(name, args, 'Int' if result == 'Proc' else result, kind == 'const')
            elif kind == 'predicate':
                name = p.pop()
                args = [t for t in p.group('(', ')') if t != ',']
                self.macros[name] = (args, p.group('{', '}'))
            elif kind in ('init', 'unsafe', 'invariant'):
                names = p.group('(', ')') if p.peek() == '(' else []
                env, bs = self.bindings(names)
                body = self.expression(p.group('{', '}'), env)
                if kind == 'init':
                    self.m.init.append(quant('forall', bs, body))
                elif kind == 'unsafe':
                    self.m.properties.append(quant('forall', bs, ['=>', distinct([x[0] for x in bs]), neg(body)]))
                else:
                    self.m.notes.append('Supplied forbidden-cube invariant retained in source only; not assumed: ' + str(names))
            elif kind == 'transition':
                name = p.pop()
                self.parameters = p.group('(', ')')
                env, bs = self.bindings(self.parameters)
                guards = [distinct([x[0] for x in bs])]
                if p.peek() in ('requires', 'require'):
                    p.pop()
                    guards.append(self.expression(p.group('{', '}'), env))
                updates = Parser(p.group('{', '}'))
                modified = set()
                while updates.peek():
                    target = updates.pop()
                    if target not in self.m.symbols or self.m.symbols[target].rigid:
                        raise Unsupported(f'invalid assignment to {target}')
                    if target in modified:
                        raise Unsupported(f'multiple simultaneous assignments to {target}')
                    modified.add(target)
                    indices = updates.group('[', ']') if updates.peek() == '[' else []
                    indices = [x for x in indices if x != ',']
                    updates.pop(':=')
                    if updates.peek() in ('.', '?'):
                        updates.pop()
                        if indices:
                            raise Unsupported('nondeterministic array update')
                    elif updates.accept('case'):
                        local, qs = self.bindings(indices)
                        if set(indices) & set(env):
                            raise Unsupported('case binder shadows parameter')
                        rhs = self.cases(updates, {**env, **local}, self.m.symbols[target].result)
                        lhs = self.m.ref(target, [x[0] for x in qs], 1)
                        guards.append(quant('forall', qs, ['=', lhs, rhs]))
                    elif indices:
                        rhs, ty = self.expr(updates, env)
                        if self.m.symbols[target].result == 'Int':
                            rhs = self.as_int(rhs, ty)
                        targets = [self.expression([x], env) for x in indices]
                        _, qs = self.bindings([f'index{i}' for i in range(len(indices))])
                        xs = [x[0] for x in qs]
                        condition = both([['=', x, y] for x, y in zip(xs, targets)])
                        guards.append(quant('forall', qs, ['=', self.m.ref(target, xs, 1), ['ite', condition, rhs, self.m.ref(target, xs)]]))
                    else:
                        rhs, ty = self.expr(updates, env)
                        if self.m.symbols[target].result == 'Int':
                            rhs = self.as_int(rhs, ty)
                        guards.append(['=', self.m.ref(target, state=1), rhs])
                    if updates.peek():
                        updates.pop(';')
                guards.extend(self.m.frame(n) for n, s in self.m.symbols.items() if not s.rigid and n not in modified)
                self.m.actions.append((name, quant('exists', bs, both(guards))))
                self.parameters = []
            else:
                raise Unsupported(f'unsupported Cubicle declaration {kind}')
        if self.ordered:
            self.m.axioms.append(['forall', [['rank_a','Proc'], ['rank_b','Proc']], ['=>', ['=', self.m.ref('__proc_rank',['rank_a']), self.m.ref('__proc_rank',['rank_b'])], ['=', 'rank_a', 'rank_b']]])
        self.m.notes += ['Process witnesses form an uninterpreted sort with injective integer rank; stored proc values are integers and may lie outside its image.',
                         'First-order encoding admits infinite domains; no finiteness axiom is added.',
                         'Action and unsafe parameters are distinct. Init parameters need not be distinct.',
                         'Updates are simultaneous; the last case branch is unconditional.']
        return self.m


def convert(text):
    return Cubicle().convert(text)
