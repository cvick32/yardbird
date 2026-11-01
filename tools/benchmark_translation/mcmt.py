"""MCMT importer matching the pinned Lambda frontend's interpretation.

Index witnesses use a separate sort and an injective integer embedding, as in
Lambda's proof export. In particular they do not range over every integer.
"""

import re
from .core import Model, Unsupported, both, either, neg, distinct, quant, safe, subst


def directives(text):
    parts = []
    ignored = {'key_search','inv_search_max_index_var','inv_search_start',
               'dynamic_predicate_abstraction','inv_search_max_num_invariants',
               'inv_search_max_num_cand_invariants','no_backward_simplification',
               'index','display_accelerated_transitions','determine_bounds','eevar',
               'variable_redundancy_test','max_transitions_number'}
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        match = re.match(r':([a-z_]+)\b(.*)', line)
        if match:
            name, rest = match.groups()
            if name in ignored:
                continue
            if name == 'comment' and not rest.strip().startswith(('index_arrays ', 'index_arrays_extra ')):
                continue
            parts.append([name, rest.strip()])
        elif parts:
            parts[-1][1] += ' ' + line
        else:
            raise Unsupported('text outside MCMT directive')
    return parts


def terms(text):
    tokens = re.findall(r'\(|\)|\[|\]|[^\s()\[\]]+', text)
    pos = 0
    def one():
        nonlocal pos
        if pos >= len(tokens):
            raise Unsupported('incomplete MCMT term')
        t = tokens[pos]
        pos += 1
        if t == '(':
            seq = []
            while pos < len(tokens) and tokens[pos] != ')':
                seq.append(one())
            if pos >= len(tokens):
                raise Unsupported('unbalanced MCMT expression')
            pos += 1
            return seq
        if pos < len(tokens) and tokens[pos] == '[':
            pos += 1
            index = one()
            if tokens[pos] != ']':
                raise Unsupported('invalid MCMT array index')
            pos += 1
            return ['read', t, index]
        return t
    result = []
    while pos < len(tokens):
        result.append(one())
    return result


class MCMT:
    def __init__(self):
        self.m = Model(sorts=['Proc'])
        self.m.add('__index_rank', ['Proc'], 'Int', True)
        self.types = {'nat':'Int', 'int':'Int', 'bool':'Bool'}
        self.signature = []
        self.index_arrays, self.extras = [], {}
        self.serial = 0

    def fresh(self, prefix):
        self.serial += 1
        return f'q_{self.serial}_{safe(prefix)}'

    def rank(self, v):
        return self.m.ref('__index_rank', [v])

    def lower(self, t, env, witnesses=None):
        if isinstance(t, str):
            if t in env:
                return env[t], 'Proc'
            if t in self.m.symbols:
                s = self.m.symbols[t]
                if s.args:
                    raise Unsupported(f'array {t} without index')
                return self.m.ref(t), s.result
            if t in ('true', 'false'):
                return t, 'Bool'
            if re.fullmatch(r'-?\d+', t):
                return (['-', t[1:]] if t.startswith('-') else t), 'Int'
            raise Unsupported(f'unknown MCMT symbol {t}')
        if not t:
            raise Unsupported('empty MCMT expression')
        op = t[0]
        if op == 'read':
            s = self.m.symbols[t[1]]
            if not s.args:
                return self.m.ref(t[1]), s.result
            idx, ty = self.lower(t[2], env, witnesses)
            if ty != 'Proc':
                if witnesses is None:
                    raise Unsupported('non-witness array index outside local guard')
                v = self.fresh('index')
                witnesses.append((v, ['=', self.rank(v), idx]))
                idx = v
            return self.m.ref(t[1], [idx]), s.result
        args = [self.lower(x, env, witnesses) for x in t[1:]]
        if op in ('=', '<', '>', '<=', '>=', '+', '-', '*'):
            # Pure index equality does not require arithmetic embedding.
            raw = [a if ty != 'Proc' or op == '=' and all(s == 'Proc' for _, s in args) else self.rank(a) for a, ty in args]
            return [op, *raw], 'Bool' if op in ('=', '<','>','<=','>=') else 'Int'
        if op in ('and', 'or', 'not', '=>'):
            return [op, *[a for a, _ in args]], 'Bool'
        raise Unsupported(f'unsupported MCMT operator {op}')

    def formula(self, text, env, witnesses=None):
        return both([self.lower(t, env, witnesses)[0] for t in terms(text)])

    def block(self, kind, entries):
        names = [v for k, v in entries if k == 'var']
        if len(names) != len(set(names)):
            raise Unsupported('duplicate MCMT variable')
        env = {n:self.fresh(n) for n in names}
        bs = [[env[n], 'Proc'] for n in names]
        if kind != 'transition':
            if any(k not in ('var', 'cnj') for k, _ in entries):
                raise Unsupported(f'unsupported {kind} directive')
            expr = both([self.formula(v, env) for k, v in entries if k == 'cnj'])
            if kind == 'unsafe':
                self.m.properties.append(quant('forall', bs, ['=>', distinct(list(env.values())), neg(expr)]))
            elif kind == 'initial':
                self.m.init.append(quant('forall', bs, expr))
            else:
                self.m.axioms.append(quant('forall', bs, expr))
            return
        if 'j' not in env:
            raise Unsupported('MCMT transition lacks update index j')
        if any(k not in ('var','guard','uguard','numcases','case','val') for k, _ in entries):
            raise Unsupported('unsupported MCMT transition directive')
        j, x, y = env['j'], env.get('x'), env.get('y')
        witnesses = []
        local = [self.formula(v, env, witnesses) for k, v in entries if k == 'guard']
        local.extend(eq for _, eq in witnesses)
        guards = [self.formula(v, env) for k, v in entries if k == 'uguard']
        if guards:
            local.append(quant('forall', [[j,'Proc']], either(([['=', j, x]] if x else []) + guards)))
        cases = []
        for k, v in entries:
            if k == 'case':
                cases.append([terms(v), []])
            elif k == 'val':
                if not cases:
                    raise Unsupported('value outside case')
                ts = terms(v)
                if len(ts) != 1:
                    raise Unsupported('case value must be one term')
                cases[-1][1].append(ts[0])
        declared = [int(v) for k, v in entries if k == 'numcases']
        if declared != [len(cases)]:
            raise Unsupported('case count mismatch')
        univ_started = not bool(x)
        for i, (conditions, values) in enumerate(cases):
            if len(values) != len(self.signature):
                raise Unsupported('case values do not match declaration order')
            special = x if i == 0 and x else y if i > 0 and not univ_started and conditions == [['=', 'y', 'j']] else None
            equations = []
            for n, value in zip(self.signature, values):
                rhs, ty = self.lower(value, env)
                if ty == 'Proc':
                    rhs = self.rank(rhs)
                lhs = self.m.ref(n, [j] if self.m.symbols[n].args else [], 1)
                equations.append(['=', lhs, rhs])
            body = both(equations)
            if special:
                local.append(subst(body, {j:special}))
                if i > 0:
                    # Mirrors Lambda's first_univ dictionary allocation.
                    univ_started = True
            else:
                condition = both([self.lower(t, env)[0] for t in conditions] + ([neg(['=',j,x])] if x and i > 0 else []))
                local.append(quant('forall', [[j,'Proc']], ['=>', condition, body]))
                univ_started = True
        params = [[env[n], 'Proc'] for n in names if n != 'j'] + [[n, 'Proc'] for n, _ in witnesses]
        self.m.actions.append((f'transition_{len(self.m.actions)}', quant('exists', params, both(local))))

    def convert(self, text):
        ds = directives(text)
        i = 0
        while i < len(ds):
            kind, value = ds[i]
            i += 1
            if kind in ('initial','unsafe','transition','system_axiom'):
                start = i
                while i < len(ds) and ds[i][0] not in ('initial','unsafe','transition','system_axiom'):
                    i += 1
                self.block(kind, ds[start:i])
            elif kind in ('local','global'):
                name, ty = value.split()
                self.m.add(name, ['Proc'] if kind == 'local' else [], self.types[ty])
                self.signature.append(name)
            elif kind == 'smt':
                ts = terms(value)
                if len(ts) != 1:
                    raise Unsupported('invalid smt directive')
                t = ts[0]
                if t[0] == 'define-type' and len(t) == 3 and t[2][0] == 'subrange':
                    self.types[t[1]] = 'Int'
                elif t[0] == 'define' and len(t) == 3 and t[2].startswith(':'):
                    self.m.add(t[1], [], self.types[t[2][1:]], True)
                else:
                    raise Unsupported('unsupported smt directive')
            elif kind == 'comment':
                bits = value.split()
                if bits[0] == 'index_arrays':
                    self.index_arrays.extend(bits[1:])
                else:
                    self.extras[bits[1]] = [str(int(v)) for v in bits[2:]]
            else:
                raise Unsupported(f'unsupported MCMT directive :{kind}')
        a, b = self.fresh('a'), self.fresh('b')
        self.m.axioms.append(['forall', [[a,'Proc'],[b,'Proc']], ['=>', ['=', self.rank(a), self.rank(b)], ['=',a,b]]])
        other = [self.m.ref(n) for n in self.index_arrays if not self.m.symbols[n].args]
        for n in self.index_arrays:
            i, j = self.fresh('index'), self.fresh('index')
            indexed = bool(self.m.symbols[n].args)
            val = self.m.ref(n, [j] if indexed else [])
            alternatives = [['=',val,self.rank(i)], *[['=',val,o] for o in other], *[['=',val, ['-',v[1:]] if v.startswith('-') else v] for v in self.extras.get(n,[])]]
            domain = either(alternatives)
            if indexed and self.extras.get(n):
                domain = both([['>=', self.rank(j),'0'], domain])
            domain = quant('exists', [[i,'Proc']], domain)
            self.m.axioms.append(quant('forall', [[j,'Proc']] if indexed else [], domain))
        self.m.notes += ['Semantics profile: pinned CADE 2021 Lambda MCMT frontend and its index-sort proof export.',
                         'nat/subrange data use Int, matching Lambda; source range bounds are not additional axioms.',
                         'Process indices use an injective integer embedding; infinite process domains are admitted.',
                         'First x-case and special y-case are local updates; remaining cases are guarded constraints.']
        return self.m


def convert(text):
    return MCMT().convert(text)
