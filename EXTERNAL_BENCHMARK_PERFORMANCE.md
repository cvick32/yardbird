# External Array Benchmark Performance

## Summary

On the external VMT sample, concrete Z3 often reaches a counterexample or a bounded-safe result while Yardbird's abstract strategy times out. The main problem is not missing array axioms or slow Z3 checks. Yardbird usually discovers too many valid instantiations, ranks them using weak relevance signals, and asserts them in large batches. The resulting refinement and e-graph work can dominate the solver.

The shortest path to better performance is:

1. rank complete array conflicts globally and assert only a small top-K batch;
2. derive relevance from the property's backward dependency cone, rather than direct property syntax;
3. use existing candidate records and cost-function hooks to score those features;
4. detect stalled refinement and invoke the concrete counterexample check earlier;
5. reduce frame multiplication and repeated e-graph work after selection improves.

## Representative evidence

All timings below use depth 20 unless otherwise noted. “Bounded-safe” is a bounded result, not an unbounded proof.

| Benchmark | Concrete Z3 | Yardbird abstract | Transition structure |
| --- | ---: | ---: | --- |
| `aws_string_eq_byte_cursor_harness.vmt` | counterexample, 0.11–0.21s | BMC/AST >10s | 1,352 definitions, 14 reads/11 writes |
| `array13_pattern.vmt` | counterexample, ~0.52s | >10s | 1,031 definitions, 2 reads/2 writes |
| `arbitrated_fifos_n2d8w8.vmt` | counterexample, 4.1–6.7s | >10s | 310 definitions, 4 reads/2 writes |
| `array_init_partial.smt2.vmt` | bounded-safe, 1.45–1.66s | >10s with all tested costs | 99 definitions, 1 read/1 write |
| `hand-simplified-array_swap-reordered.vmt` | bounded-safe, 6.7–7.0s | >10s with all tested costs | 244 definitions, 6 reads/6 writes |

The important commonality is that none of these five properties contains an array read or write syntactically. Each property is expressed through scalar state whose transition definitions depend on arrays. Consequently, exact membership in `property_terms` is almost never a useful relevance feature for these generated problems.

### Controlled comparisons

- **AWS, depth 2:** concrete Z3 finds the counterexample immediately. BMC cost and AST size still exceed 12s, while Adaptive and Split find it in about 0.64s. BMC cost continues generating conflicts after 22 refinement steps and can produce 86 high-cost instances in one step. Adaptive and Split exhaust useful conflicts after eight steps and reach the existing concrete check.
- **`array_init_partial`:** target depth 7 completes in 0.97s, but target depth 8 exceeds 12s. On the last successful depth, solver checks take roughly 3–14ms while array saturation alone grows to 429ms.
- **Array swap:** at the failing depth, successive refinements produce high-cost batches of 23, 40, 46, 60, 64, and 134 instances.
- **Frame-policy check:** `no-unroll-on-loop` does not rescue AWS, either bounded-safe case, or the hardware case under 12s. Framing contributes to growth but is not the primary cause.
- **`array13_pattern`:** the concrete counterexample first appears at target depth 7. At that exact depth, BMC cost takes 9.9s and Split takes 8.1s, while AST and Adaptive still exceed 12s. This is highly sensitive to candidate ordering despite there being only two reads and two writes.

Raw Garden results:

- `benchmark_results/main_eval/external-array-panic-fixes-final-depth20-local-20260807_170433/raw/external-depth20/08_07_2026_17_04.json`
- `benchmark_results/main_eval/external-cost-functions-depth20-local-20260807_194332/raw/external-cost-functions-depth20/08_07_2026_19_43.json`
- `benchmark_results/main_eval/external-cost-functions-depth20-local-20260807_194332/raw/external-cost-functions-z3-depth20/08_07_2026_19_53.json`

## Diagnosis

### Cost functions act at the wrong level

`ArrayTermExtractor` uses cost to choose an e-class representative, but `ArrayConflictScheduler` processes conflicts in enumeration order. It does not enumerate complete conflicts and rank them globally. Cost therefore determines how a particular conflict is rendered more than which conflict Yardbird should try next.

The scheduler classifies cost >= 100 as `ConstOrHighCost`, but `Abstract::finish` still asserts those instances immediately. The threshold changes batching rather than deferring or rejecting poor candidates. This explains the very large batches seen in the swap and AWS traces.

Relevant code:

- `src/theories/array/array_term_extractor.rs`
- `src/theories/array/array_conflict_scheduler.rs`
- `src/strategies/array_abstract.rs`

### Property relevance is too syntactic

Current costs see property subterms and transition subterms, but not the dependency path connecting them. `SplitCost` specifically extracts array index variables that appear directly in the property. That set is empty for all five cases, so its specialized synthesis is inactive. Its AWS improvement comes from generic operation weights shared with Adaptive, not from its split-specific logic.

### Poor choices create a growth loop

Each SAT refinement evaluates every accumulated initial, transition, property, and instantiation subterm in the model and constructs a fresh e-graph. New instantiations are themselves added to the subterm set. Poor selections therefore increase the cost of every later refinement.

`FullUnroll` deduplicates abstract instances, while `NoUnrollOnLoop` currently does not. This is a secondary performance hazard, although the frame-policy experiment shows it is not the main bottleneck.

## Recommended implementation plan

### 1. Add conflict-level top-K scheduling

Enumerate candidate axiom conflicts before asserting any of them, score the complete conflicts globally, and assert only the best one or a small batch per refinement. Keep three concepts separate:

- e-class representative extraction cost;
- complete conflict priority;
- assertion/defer/drop policy.

Replace the implicit cost-100 batching rule with an explicit deferred queue and configurable batch cap. This is the smallest change likely to help both counterexample and bounded-safe cases.

### 2. Compute a property dependency cone

Starting with state variables referenced by the property, walk backward through next-state relationships and transition definitions. Record the array reads, writes, indices, values, and guards that can influence the property. Preserve distance from the property and frame information.

For a current abstract counterexample, refine this static cone with model-evaluated guards so operations on the active control path rank first.

### 3. Extend the existing cost-function features

Add the following to `TermFeatures`, `CandidateRecord`, and the logistic-regression feature set:

- membership in the property dependency cone;
- distance from the property;
- membership on the current model's active path;
- array/index relationship to a cone-relevant read or write;
- distance from the failing frame;
- prior selection count and whether the selection eliminated a model;
- source axiom kind.

Use a deterministic `PropertyConeCost` first. The existing decision logging and logistic-regression infrastructure can learn a ranker later without creating a new data pipeline.

### 4. Add progress-aware concrete checks

Run the existing concrete counterexample check when Yardbird repeats a model fingerprint, produces only deferred/off-cone candidates, or adds no cone-relevant information for a small number of steps. This prevents a real counterexample from being delayed indefinitely merely because another irrelevant theory instance exists.

### 5. Control frame multiplication

Deduplicate in shared instantiation storage so every unroll policy has the same behavior. Initially materialize an instance only at frames participating in its conflict or dependency slice, expanding the range if refinement stalls.

### 6. Reduce repeated e-graph work

After reducing the number of refinements, cache translated static subterms and the static e-graph skeleton. Update only model equivalences and newly added instances. This should address the saturation cliff in `array_init_partial` without obscuring the more important selection improvements.

## Validation

Develop against the five cases above, then run the full set of 17 benchmarks where concrete Z3 is decisive and Yardbird times out, followed by the deterministic 200-problem sample.

Track:

- decisive results within 10s;
- median and p95 runtime;
- refinement count and total asserted instances;
- maximum per-refinement batch size;
- time in model update, saturation, and solver checks;
- e-graph nodes and accumulated subterms.

Every abstract counterexample must still be confirmed by concrete Z3. The initial targets should be AWS depth 2 under 1s, both bounded-safe cases at depth 20 under 10s, and a net recovery of Z3-only results without losing existing Yardbird successes.
