# Demand-Guided Instantiation Plan

Status: evidence-informed proposal

## Goal

Reduce unnecessary array instantiations by preferring formulas that lie on the
data-flow path from the failing property back to the array writes that can
determine it.

The first version remains a one-formula-per-refinement strategy:

```text
failing property read/value
              ↓
backward data-flow demand
              ↓
rank matching array-axiom candidates
              ↓
add the best demanded formula
              ↓
new model either proves progress or exposes the next demand
```

This plan does **not** initially generate a batch of consequences for a nested
write chain. Demand changes which existing candidate is selected first. It does
not add a second source of instantiations.

## What Counts as Demand

A demand is a frame-aware request for a value that matters to the current
counterexample. The initial roots come from the negated property at the current
BMC depth:

- array reads used by the property;
- their index expressions;
- scalar values and predicates that consume those reads; and
- helper definitions reachable from those expressions.

Walk backward from those roots through:

- zero-argument helper definitions;
- current/next-state assignments in the transition relation;
- `Read(array, index)` dependencies;
- `Write(base, index, value)` dependencies; and
- scalar dependencies in array indices and written values.

The result is a small demand graph. Each node retains its BMC frame and edge
kind so that “same symbol at another frame” is not treated as equally relevant.

For example, if the property depends on `Read(B@k, j@k)` and the transition
defines `B@k` from `Write(A@(k-1), i@(k-1), v@(k-1))`, candidates connecting
that write to the demanded read should outrank unrelated reads and writes from
the same model.

## Current Seams

The necessary information is already present, but it is currently flattened:

- `SubtermHandler` keeps property, transition, initial, and instantiation
  subterms separately:
  [subterm_handler.rs](../src/subterm_handler.rs).
- `ReadsAndWrites` records array/read/index and array/write/index/value tuples:
  [reads_and_write.rs](../smt2parser/src/vmt/reads_and_write.rs).
- `DefinitionGraph` and `DefinitionMaterializer` preserve helper-definition
  dependencies:
  [definition_graph.rs](../smt2parser/src/vmt/definition_graph.rs) and
  [definition_materializer.rs](../smt2parser/src/vmt/definition_materializer.rs).
- `ArrayConflictScheduler` already enumerates candidate axiom violations and
  asks the extractor to choose concrete terms:
  [array_conflict_scheduler.rs](../src/theories/array/array_conflict_scheduler.rs).

Do not hide the demand graph inside a new monolithic cost function. Build it as
a small analysis object that can annotate candidates, then retain the existing
BMC cost as the tie-breaker and fallback.

## Candidate Ranking

Begin with a tiered rank rather than a hard filter:

1. **Direct demand:** the candidate explains a demanded read over the write that
   defines its array value at the relevant frame.
2. **Demand predecessor:** the candidate exposes a read or written value that is
   the next predecessor on a demanded path.
3. **Index/value support:** the candidate uses an index or value expression on a
   demanded path but does not directly connect the demanded read and write.
4. **Unrelated:** no known connection to the current demand graph.

Within a tier, prefer:

- shorter graph distance to the property;
- exact array and index-expression matches;
- closer frame alignment;
- terms already present in the property or transition formula; and then
- the existing BMC cost and deterministic textual tie-breaking.

The fallback is essential. If no candidate is demand-related, use the current
selector unchanged. This preserves refinement progress while the graph analysis
is incomplete.

After adding the selected formula, update the demand frontier from the next SAT
model. Do not eagerly walk the whole graph and assert every formula on it. The
next model tells us which predecessor is actually still missing.

## Smaller Equality-Reduction Changes

These should be evaluated before or alongside the ranker because they are
narrower and easier to attribute.

### 1. Eliminate exact read-after-write formulas before abstraction

Implement the exact syntactic rewrite already specified in
[array-preprocessing-optimizations.md](array-preprocessing-optimizations.md):

```text
select(store(A, i, v), i)  ->  v
```

This removes an array term that would otherwise require a read-after-write
equality instance. It is the lowest-risk first change.

### 2. Canonicalize and deduplicate asserted equalities

Count ground equality assertions before changing behavior. Then canonicalize
the two sides for deduplication so syntactic variants such as `a = b` and
`b = a` share an identity. Apply deduplication after BMC indexing and helper
materialization, because that is the formula Z3 actually receives.

Keep separate counts for:

- abstract theory instances;
- indexed theory equalities;
- helper-definition equalities; and
- unique assertions accepted by Z3.

Do not infer from Z3's `added eqs` counter that Yardbird asserted the same
number of equality formulas. `added eqs` counts internal equality-processing
attempts, not input assertions.

### 3. Place instances only on demanded frames

The current full-unroll policy can materialize a newly found instance at every
eligible historical frame and then at later frames. Once candidate provenance
contains a demanded path and frame, compare full unrolling with asserting the
instance only at frames touched by that path.

This is a direct way to reduce indexed equality assertions. It should follow the
rank-only experiment because frame restriction changes placement and can add
refinement rounds if the demand slice is incomplete.

### 4. Slice model/e-graph equalities only after ranking works

`ArrayRefinementState::update_with_subterms` currently evaluates every collected
non-Boolean subterm and unions it with its model value in the e-graph. A later
experiment can begin with demanded subterms and widen to all subterms on no
progress.

This reduces e-graph model equalities and candidate-search work; it does not
directly reduce Z3 input equalities. Keep those measurements distinct.

## Evidence From the Depth-50 Evaluation

The full evaluation gives the ranker a clear optimization target. See
[z3-deep-clean-solver-stats.md](z3-deep-clean-solver-stats.md).

- Abstract's large aggregate Z3 win is concentrated in expensive solves. The
  new selector must preserve the formulas that prevent the hard-tail search
  state from exploding.
- On end-to-end wins, abstract had substantially fewer decisions, added
  equalities, resource work, clauses, and Boolean variables in aggregate. Those
  are better primary signals than raw conflict count.
- Conflicts are not equal-cost events. Do not optimize the demand score directly
  for fewer conflicts.
- `array_split_20` and `array_split_21` are already 21--26x faster in Z3 under
  abstraction but lose roughly 50--68 seconds outside `check_sat`. They are
  useful for testing whether better ordering reduces repeated Yardbird search.
- `array_nonlin_square` is a genuine solver regression and should guard against
  a ranking rule that prefers formulas producing expensive arithmetic search.

## Experiment Order

1. **Baseline counters.** Record candidate count, selected candidate, demand
   tier/distance in shadow mode, abstract instances, indexed equalities,
   helper-definition equalities, unique Z3 assertions, checks, and timing.
2. **Exact read-after-write preprocessing.** Measure it alone so its equality
   reduction is attributable.
3. **Shadow demand ranking.** Build the property-rooted demand graph and log what
   it would select without changing the current choice.
4. **Rank-only demand selection.** Still emit exactly one formula per refinement
   and retain the current selector as fallback.
5. **Canonical ground-equality deduplication.** Measure how many real duplicates
   exist before relying on it for a performance claim.
6. **Demand-local frame placement.** Compare with full unrolling after the
   selected formula has stable frame provenance.
7. **Demand-sliced e-graph population with widening fallback.** Attempt only if
   candidate search remains a material cost after the earlier changes.

Do not begin with top-k selection or eager formula generation. Those conflate
formula quality with batching and move away from the goal of fewer
instantiations.

## Target Cohorts

Use a small stratified set before a full sweep:

- **Yardbird-search targets:** `array_split_20` and `array_split_21`.
- **Solver-regression targets:** `array_nonlin_square` and the other
  nonlinear/decision-heavy losses identified by the paired report.
- **Hard-tail guardrails:** `array_tiling_tcpy2`, `array_tiling_tcpy3`, and
  `array_init_addvar7`.
- **Simple attribution cases:** benchmarks containing exact
  `select(store(...), same-index)` patterns.

## Validation and Stop/Go Criteria

Correctness requires identical bounded outcomes and no lost counterexamples.

Primary measurements are paired per benchmark:

- abstract and indexed instantiation counts;
- unique equality assertions sent to Z3;
- refinement checks per depth;
- time outside `check_sat`;
- Z3 time and total wall time; and
- decisions, resource count, added equalities, clauses, and Boolean variables.

Use conflicts and propagations as secondary explanations.

Advance the demand ranker if it reduces instantiations or repeated Yardbird work
without moving Z3's hard-tail curve backward. A modest median improvement is
not enough if the existing large tail wins regress.

Advance frame-local placement only if it materially reduces indexed assertions
without widespread extra refinement. Stop a restriction or slicing experiment
when it repeatedly falls back to the full set or increases checks enough to
erase the assertion reduction.

For timing claims, repeat the target cohort locally before a full benchmark
sweep. The full report should include the Z3-only cactus plot and the paired
Z3-versus-end-to-end boundary plot.

## Implementation Steps

1. Add a frame-aware `DemandGraph` analysis over property, definition, and
   transition dependencies.
2. Annotate scheduler candidates with demand tier, graph distance, array/index
   match, and frame match.
3. Log the annotations in shadow mode using existing decision provenance.
4. Add a demand-first comparator ahead of the existing BMC-cost tie-breaker.
5. Implement the exact preprocessing rewrite and ground-equality counters as
   independent changes.
6. Add canonical ground-equality deduplication if the counters show duplicates.
7. Add demand-local frame placement as a separate experimental policy.
8. Add demanded-subterm e-graph slicing only if profiling still justifies it.

## Expected Effort

- Demand graph and shadow annotations: 2--4 days.
- Rank-only selection experiment: 2--3 days.
- Exact preprocessing and equality counters: 1--2 days.
- Equality deduplication, if justified: 1--2 days.
- Demand-local frame placement: 2--4 days.
- Benchmarking and analysis: 2--4 days.
