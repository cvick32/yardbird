# Demand-Guided Instantiation Plan

Status: proposal

## Goal

Reduce SAT/SMT round trips by giving the solver more useful theory information
after the cost function selects a good conflict.

The central idea is:

```text
cost function selects one seed
              ↓
DemandClosure derives its direct consequences
              ↓
unrolling policy places the instances into BMC frames
              ↓
solver checks the stronger formula
```

The heuristic remains human-interpretable: the cost function chooses what
matters. Demand closure performs deterministic theory reasoning after that
choice.

## Current Seams

The array scheduler currently stops after finding one regular conflict:
[array_conflict_scheduler.rs](../src/theories/array/array_conflict_scheduler.rs#L246-L285).
That preserves the existing one-seed cost-function decision.

The selected array expressions are returned to `Abstract::finish`, converted to
SMT terms, and added to the problem:
[array_abstract.rs](../src/strategies/array_abstract.rs#L232-L361).

`InstantiationStrategy` already has two lifecycle hooks:

- `on_generate`, when an instance is found;
- `on_loop`, when BMC advances to another depth.

See
[instantiation_strategy/mod.rs](../src/instantiation_strategy/mod.rs#L18-L60).

The main refactor is to make "instance found" a first-class event carrying enough
information for deterministic expansion.

## Instantiator Shape

Treat instantiators as composable policies with two events:

```rust
trait Instantiator {
    fn on_find(&mut self, found: FoundInstantiation, context: &mut Context);
    fn on_loop(&mut self, depth: u16, context: &mut Context);
}
```

The existing policies remain simple:

- `FullUnroll` handles a found instance using its current frame expansion and
  handles later BMC depths using its current loop behavior.
- `NoUnrollOnLoop` handles a found instance but does nothing extra on a loop.

`DemandClosure` wraps one of those policies:

```text
DemandClosure<FullUnroll>
DemandClosure<NoUnrollOnLoop>
```

On `on_find`, it derives the closure and passes every resulting instance to the
wrapped policy. On `on_loop`, it simply delegates. This keeps theory expansion
separate from frame placement.

## Seed Information

The scheduler should return a `FoundInstantiation` containing:

- the selected lemma;
- its axiom and cost-function provenance; and
- an optional theory-specific seed.

For the first implementation, the only special seed is an array read over a
write:

```text
Read(Write(A, i, v), j)
```

The seed must contain stable expressions, not `egg::Id` values. The e-graph is
recreated for every refinement step in
[array_abstract.rs](../src/strategies/array_abstract.rs#L201-L220).

## Demand Closure

Version one walks only the explicit write chain in the selected expression:

```text
Read(Write(Write(A, i1, v1), i2, v2), j)
```

For each write edge it emits the valid equality:

```text
Read(Write(A, i, v), j)
    = ite(i = j, v, Read(A, j))
```

When `i` and `j` are exactly the same expression, it may emit the simpler:

```text
Read(Write(A, i, v), i) = v
```

Otherwise it keeps the `ite`; it does not guess equality or disequality from the
current SAT model.

Use a small fixed internal step limit initially, such as eight writes. Record
when the limit is reached, but do not add another normal user-facing option until
there is evidence that users need it.

## Implementation Steps

1. Refactor the instantiator interface around `on_find` and `on_loop` without
   changing behavior.
2. Preserve the selected array conflict as a stable `FoundInstantiation`.
3. Implement `DemandClosure` for explicit read/write chains.
4. Pass the seed and all derived instances to the wrapped unrolling policy.
5. Add exact instance deduplication before solver assertion.
6. Compare baseline, `DemandClosure<FullUnroll>`, and
   `DemandClosure<NoUnrollOnLoop>`.

## Cost-Guided Multiple Seeds

Selecting the best several conflicts before returning to the solver is a logical
follow-up, but it changes the heuristic story more than demand closure does.

Evaluate it only after single-seed demand closure:

1. Baseline: one seed, no closure.
2. One seed with demand closure.
3. Top-k cost-ranked seeds without closure.
4. Top-k seeds with closure, only if both ideas help independently.

Top-k should use the existing cost function ranking and retain a readable record
of why every seed was selected.

## Validation

Unit tests should cover one write, nested writes, exact same indices, unknown
index relations, closure limits, and duplicate instances.

Benchmark measurements should include:

- solver checks per BMC depth;
- total and unique instances;
- indexed assertions;
- solver time and total wall time; and
- timeouts and verification outcomes.

The change is successful if it substantially reduces solver checks or solver
time without correctness differences or widespread instance growth. Adding more
lemmas is not itself a win; the solver must benefit from them.

## Expected Effort

- Interface refactor with unchanged behavior: 2–3 days.
- First explicit-chain demand closure: 3–5 days.
- Benchmarking and tuning: 2–4 days.
- Top-k seed selection, if pursued: another 2–4 days.
