# Array Preprocessing Optimization Plan

Status: proposal

## Goal

Remove obvious array expressions before Yardbird converts native array operations
into uninterpreted functions. This is a small engineering optimization, separate
from Yardbird's cost-guided instantiation work.

## Scope

Start with one rewrite:

```text
select(store(A, i, v), i)  ->  v
```

This is useful because Z3 would normally simplify it using native array
semantics, but Yardbird loses that built-in behavior after array abstraction.

A second, experimental rewrite may combine complementary guarded stores:

```text
(c  => X = store(A, i, v1))
and
(!c => X = store(A, i, v2))

        ↓

X = store(A, i, ite(c, v1, v2))
```

The guarded-store rewrite should be pursued only if benchmarks show that the
pattern is common and beneficial.

This plan does not include:

- arithmetic or affine index reasoning;
- model-dependent simplification;
- quantifier instantiation;
- e-graph changes; or
- solver assertion management.

## Design

Add a small bottom-up simplifier in:

```text
smt2parser/src/vmt/array_term_simplifier.rs
```

The generic rewriter already visits children before their parent:
[rewriter.rs](../smt2parser/src/rewriter.rs#L18-L67).

Use one narrow interface:

```rust
pub fn simplify_array_term(term: Term, mode: ArraySimplificationMode) -> Term;
```

Run it before `ArrayAbstractor` replaces `select` and `store`:
[array_abstractor.rs](../smt2parser/src/vmt/array_abstractor.rs#L292-L366).

Wire the same simplifier into both entry paths:

- VMT abstraction:
  [vmt/mod.rs](../smt2parser/src/vmt/mod.rs#L153-L173)
- SMT-LIB abstraction:
  [smtlib_problem.rs](../src/smtlib_problem.rs#L182-L203)

Keep the mode internal while benchmarking. This should not become another
permanent user-facing knob: either a rewrite proves broadly safe and useful, or
it remains experimental.

## Implementation Steps

1. Count same-index reads and guarded-store pairs in representative benchmarks.
2. Implement exact same-index read-after-write simplification.
3. Add VMT and SMT-LIB tests, then measure abstract strategy performance.
4. Make the exact rewrite unconditional if it has no correctness or performance
   regressions.
5. Implement guarded-store factoring only if the initial measurements justify
   it.

## Priority From the Depth-50 Evaluation

The exact same-index rewrite should be tested before broader demand-guided
selection. It directly removes a read/write term and the equality instance that
would otherwise explain it, making the result easy to attribute.

Keep guarded-store factoring second. Although it may combine duplicate store
structure, it introduces an `ite`; the depth-50 evaluation shows that preserving
the abstract strategy's smaller clause and Boolean-variable state is important
to its hard-tail wins. Count the pattern first and accept the rewrite only when
it reduces asserted equalities without increasing Z3 decisions or resource
work on the paired benchmarks.

Report this preprocessing result separately from demand-guided ranking. The
preprocessor changes the input formula, while the ranker changes which valid
array formula Yardbird selects next.

## Correctness Rules

- Match indices by exact AST equality only.
- Rewrite only native array operations before abstraction.
- Never use a SAT model or e-graph equality as proof.
- For guarded stores, require exact complementary guards, the same target,
  array, and index, and sibling implications in one positive conjunction.
- Leave ambiguous patterns unchanged.

## Validation

Tests should cover exact and different indices, nested stores, bit-vector
indices, quantifier bodies, and both input modes.

For guarded-store factoring, ask the concrete solver to prove the original and
rewritten formulas equivalent.

The optimization is accepted only if:

- concrete and abstract verification results remain unchanged;
- the snapshot suite passes after manual review;
- no new timeouts appear; and
- the targeted benchmarks show less refinement or lower solver time.

## Expected Effort

- Exact read-after-write simplification: 1–2 days.
- Guarded-store factoring and evaluation: another 2–4 days if justified.
