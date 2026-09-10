# Auxiliary policy implementation plan

Status: reviewed proposal; no solver implementation in this change.

## Recommendation and estimated size

Implement an opt-in stable property-index shadow encoding first, then evaluate a repaired repetition trigger independently. Reuse the existing array encoding seam and stability analysis. A shadow represents the value at an arbitrary property index, so its update condition follows from the program's writes and requires no interpolant capture predicate.

Expected added/changed lines, excluding generated results and this document:

| Work package | Implementation / tooling | Tests | Total |
|---|---:|---:|---:|
| 1. Reproducible candidate inventory and eligibility report | 150–200 | 60–100 | 210–300 |
| 2. Shadow projection, certification, and model rewriting | 450–650 | 280–380 | 730–1,030 |
| 3. CLI, Garden, result identity, and report integration | 110–170 | 70–110 | 180–280 |
| 4. Repair repeated-pattern selection and accounting | 180–260 | 120–170 | 300–430 |
| 5. Benchmark configurations and comparison tooling | 50–80 | — | 50–80 |
| **Total** | **940–1,360** | **530–760** | **1,470–2,120** |

Budget about **1,800 lines** for the complete experiment. Packages 1–3 and 5 make the first independently runnable shadow experiment: **1,170–1,690 lines including tests**. These are estimates of authored lines, not a promise of net repository growth; some trigger code will be replaced. Multiple arrays sharing one index and nested stores are included in the projection implementation, rather than separate synthesis frameworks.

## Corrections to the earlier analysis

The principal source is `benchmark_results/main_eval/array-depth50-aux-interpolant-aws-20260903_223321/raw/array-best-depth50/09_03_2026_22_33.json`. The comparison source is `benchmark_results/main_eval/array-depth50-property-check-ablation-aws-20260901_123135/raw/array-best-depth50/09_01_2026_12_31.json`.

1. `used_instances` means retained refinement schemas. `Abstract::result()` fills it from `ProblemContext::get_instantiations()`, which returns every stored instance. The September 3 results contain no UNSAT-core data. Calling these "proof-used" was too strong. All 163 successful results also have `found_proof=false`: success here is bounded checking through the requested depths, not an inductive proof.
2. The previous count of 16 nonlocal benchmarks examined the read/write index pair. Counting frames in the whole retained schema gives **19**, including array/value terms. This matches the kind of locality test the actual trigger uses more closely.
3. A concrete frame gap does not prove a loop recurrence or justify a fixed-delay history variable. Phase changes, resets, and stuttering can alter the relation. Remove the proposal to derive captures from frame gap alone.
4. A repetition threshold filters existing opportunities. It does not, by itself, enlarge the scalar-only capture target supported by `AuxiliarySynthesisCandidate`, repair localization, or make a rejected interpolant useful. The eleven index-nonlocal benchmarks without installed auxiliaries are not eleven established trigger failures.
5. High retained counts can follow an unhelpful auxiliary. `array_init_ite_dupl` has 9 schemas / 450 indexed assertions in September 1 and 144 / 6,987 in September 3. These runs use different revisions, so use this as evidence of workload sensitivity, not as an isolated causal measurement.
6. Historical counts cannot serve as a startup runtime trigger. The first shadow experiment uses an explicit option and an offline-selected cohort. Installing after a live repetition threshold would require a separate design for retroactive constraints and solver state.

### Audited screening counts

The September 3 run has 189 results: 163 successful, 11 errors, and 15 timeouts. Of the successful results, 130 have nonempty retained-schema lists, totaling 1,033 schemas. Coverage below counts benchmarks, not schemas.

| Screening feature | Benchmarks / 189 | Fraction of all benchmarks | Fraction of 130 with retained schemas |
|---|---:|---:|---:|
| Auxiliary installed in the historical run | 5 | 2.6% | 3.8% |
| Nonlocal read/write indices | 16 | 8.5% | 12.3% |
| Any nonlocal frames in the whole schema | 19 | 10.1% | 14.6% |
| At least 3 distinct schemas sharing array/index-pair shape | 22 | 11.6% | 16.9% |
| At least 8 retained schemas | 44 | 23.3% | 33.8% |
| Union: pressure ≥8, index nonlocality, or repetition ≥3 | 49 | 25.9% | 37.7% |

The repetition screen erases numeric frame suffixes from array and index terms, retains the array name and index expression shape, and counts distinct retained schema entries per group. This is an offline screening key, not a rule for identifying equivalent instances.

A stricter read-only source check found a matching retained `Read(Write(...), q)` at a property index in **127/189 (67.2%)**, using only a simple scalar index with an unconditional `q_next = q`, or a literal. It found 144 array/index pairs. All 44 high-schema cases belong to that set. This establishes broad candidate syntax, not that the proposed transition projector can handle every assignment. Guard coverage, sorts, dependencies, and size limits must still pass.

September 1 has 183 successful results, 150 nonempty schema lists, and a corresponding pressure/repetition/nonlocal screening union of 61/189 (32.3%). The difference reinforces the need for a fresh same-revision baseline. Budget the first targeted evaluation around **49 historical candidates, about 26% of the suite**; do not label that an expected speedup percentage. All 26 September 3 failures stay in the eventual full-suite evaluation.

## 1. Reproducible inventory and eligibility report

Proposed file: `scripts/analyze_auxiliary_policy_candidates.py`, with focused tests under `tests/`.

- Read the two run artifacts and emit benchmark lists and a small JSON report. Record run IDs, commits, solver settings, denominators, and the exact screening predicates.
- Parse S-expressions structurally, including quoted symbols and nested bindings; recognize stored `x+N` instance offsets separately from live `x@N` symbols.
- Distinguish retained schemas, indexed placements, selected conflicts, and available core membership. Missing core data remains unknown.
- Count each distinct schema once per pattern. Automatic placements from `full-unroll` must not count as new synthesis evidence.
- Include a checked 49-benchmark cohort and a no-auxiliary baseline cohort. Actual shadow eligibility comes from the Rust encoding report in package 2, so Python does not become a second semantic certifier.

Acceptance: regenerate the counts above; a fixture with repeated frame placements does not inflate the count; a schema whose array/value spans frames is identified even when its index pair is local.

## 2. Stable property-index shadow encoding

Proposed module: `src/theories/array/encodings/property_shadows.rs`. Integrate through `EncodingPlan::apply` in `encodings/mod.rs`, after the existing recurrent-product pass and before the strategy builds its term catalog and property cone. This pass transforms the abstract VMT model, with correctness justified against concrete array semantics.

Keep one small module interface:

```rust
fn encode_property_shadows(
    model: VMTModel,
    array_types: &[(String, String)],
) -> (VMTModel, PropertyShadowReport)
```

The report records candidate array/index pairs, accepted pairs, generated scalars, rewritten reads, and specific rejection reasons. Keep projection details private. `EncodingPlan` may need to lose `Copy` if it retains structured records; do not add a generic synthesis-plugin abstraction.

### Supported first slice

- Abstract VMT strategy, one-dimensional `Array Int Int`.
- Property observations `Read(A, q)` where `q` is a scalar state certified unchanged on every enabled transition, an immutable declaration, or an integer literal.
- At most one chosen index per run, selected deterministically by property occurrence count and then a stable lexical key. Transform all needed arrays at that index as one group. Leave other property observations intact.
- Direct and guarded assignments of current arrays, stores, nested stores, constant arrays, and supported array-valued `ite` expressions. Guards and right-hand sides must be supported current-state expressions.
- Close the group over current-array aliases and the reads at `q` needed by write values. Put a small explicit limit on closure size (initially four arrays) and generated expression size; reject the whole group if it cannot be represented consistently.
- Reject uncovered assignment paths, unsupported sorts, quantified/lambda expressions, unsupported helper definitions, unresolved next-state dependencies, or a changing index. Never infer stability from capitalization.

Reuse `certified_stable_states` in `encodings/stability.rs`. Extend the assignment scanner to return certified `(guard, value)` assignments as well as the current values-only view. Preserve the existing `exhaustive_next_assignments` interface for recurrent products. Keep the conservative coverage proof; do not interpret several implication guards as an ordered `if/else`.

### Generated equations and property substitution

For each accepted pair `(A, q)`, create a fresh scalar `h_A_q` and its next-state declaration. Initialize it with the original read:

```text
h_A_q(0) = Read(A(0), q)
```

Preserve the existing initial constraints. Do not accidentally rewrite this bridge into `h = h`.

For an assignment `g => A_next = store(A, j, v)`, generate:

```text
g => h_A_q_next = ite(j = q, value_at_q(v, j = q), h_A_q)
```

For a carry, generate `g => h_next = h`. For a copy from `B`, use `h_B_q`. For a constant array, use its constant element. Project nested stores recursively, respecting the outermost write's priority. Each write value is evaluated against the array expression it actually reads, not an accidentally mutated accumulator.

Rewrite exact accepted reads in the property to shadows. Within generated recurrences, replace reads at the watched index with the corresponding shadow. In a store's equality branch, also simplify a read at that store index using the branch fact. For example:

```text
A_next = store(A, i, Read(A, i) + 1)
h_next = ite(i = q, h + 1, h)
```

This branch-aware simplification matters: leaving `Read(A, i)` in the recurrence can preserve much of the original refinement burden. It is valid only under the matching-index condition and for the correct source array. Other unhandled reads remain reads.

Add `VMTModel::replace_property_condition_for_yardbird`, preserving VMT attributes, alongside its existing transition replacement method. Build the complete encoding group before mutating the model. Keep original array transitions available for remaining observations and refinement; the initial experiment does not delete accumulated instances or require changes to incremental session installation.

### Correctness obligations and tests

The key invariant is `h_A_q = select(A, q)` in the concrete interpretation. Establish:

1. Every original initial state extends to the generated initial constraints.
2. Under that invariant, every original enabled transition extends to all generated recurrences and preserves the invariant.
3. Under that invariant, the original and rewritten properties agree.

Use concrete-array solver checks of these obligations and small counterexample fixtures. Check initial index/value correlation, changing indices, missing guard coverage, overlapping guarded assignments, nested writes to the same index, copying between arrays, read-modify-write values, constant arrays, and fresh-name collisions. Unknown certification or unsupported syntax rejects the candidate.

The existing driver retains the original concrete model before `configure_model`; keep that path for counterexample validation. Bounded agreement tests alone do not replace the invariant argument. Validate exported transformed VMT as well, because `Abstract::result` sends that model to IC3IA when requested.

## 3. Options, serialization, and reporting

Files: `src/lib.rs`, `src/strategies/array_abstract.rs`, `src/theories/array/encodings/mod.rs`, `garden/src/config.rs`, `garden/src/main.rs`, `paper-graphics/src/benchmark_parsing.py`, and the relevant report tests.

- Add `--encode-property-shadows`, default off; Garden configuration `encode_property_shadows: true`.
- Forward and serialize the option in every subprocess result. Include it in strategy identity so reports cannot merge shadow and baseline measurements.
- Also include the already-existing predicate relevance and refinement retention dimensions when comparing synthesis policies; they are missing from the current Python result model.
- Expose generated-shadow and rejection counts through the existing encoding statistics path; retain detailed pair/rejection data in a structured diagnostic artifact.
- Reject the option clearly for unsupported modes rather than silently applying a partial variant.
- Reuse existing profiling, solver statistics, and tracked-instance facilities. Collect cores in separate diagnostic runs; do not compare tracked diagnostic timing with an untracked baseline.

Acceptance: CLI/Garden round-trip tests, old result JSON still loads, new configurations have distinct report identities, and the default model remains unchanged.

## 4. Repair repeated-pattern synthesis separately

Files: `src/auxiliary_synthesis/trigger.rs`, `conditional_history.rs`, and focused trigger tests. Reuse the existing `repeated-pattern` option and threshold flag.

Current limitations: the trigger selects the first nonlocal conflict, updates only that conflict's counter, and normalizes with whitespace/token operations. Installation deduplication uses a transient conflict ID. These choices make repetition sensitive to candidate order and offer little control over repeated attempts.

Implementation:

- Observe every eligible selected conflict in a batch. Count distinct refinement events, once per family per event; do not count the number of equivalent candidates or indexed placements.
- Derive AST keys using axiom identity, sorts, array identity, index structure, and temporal roles. Keep a relative-offset schema key and a coarser family key separately. Preserve actual offsets and concrete terms for synthesis; family membership never authorizes substituting one instance for another.
- Start with threshold 3. Record both distinct event count and depth count; do not initially require three different depths, which could suppress a case stuck refining at one depth.
- Prefer source-grounded evidence, then distinct-event support and nonlocality, with deterministic tie breaking. Try the next eligible candidate when the leading candidate cannot be localized or guarded, within a bounded attempt budget.
- Deduplicate installed auxiliaries by their actual semantic specification (capture, guard, mode, and localized axiom), not conflict occurrence ID. Retry rejected families only on fresh evidence, with a short cooldown.
- Retain the current concrete validation and predicate qualification. This change makes attempts more deliberate; it does not claim to expand the supported auxiliary variable kinds.

Tests: reorder a batch without changing the decision; repeat several candidates in one event without inflating counts; detect a repeating family when the first candidate keeps changing; preserve quoted/signed frames and distinct index relations; avoid reinstalling an equivalent auxiliary under a new conflict ID; bound retries after rejection.

This package is independent of startup shadows. Evaluate it independently before enabling both features together. Combining them also requires teaching auxiliary-symbol detection about generated shadow variables to prevent recursive synthesis on instrumentation.

## 5. Evaluation and decision gates

Use one current release build, the same hardware, depth 50, 120-second timeout, BMC cost, source-then-full, prefer-source, 16 winners, assumptions, and full-unroll. Record exact options and revision. Historical AWS wall times are context, not the timing baseline for this experiment.

First local panel:

- Simple controls: `array_copy`, `array_init_const`, `array_init_batches`.
- Read-modify-write / phases: `array_init_addvar`, `array_init_increm`, `array_init_increm_twice`.
- Multiple arrays: `array_init_increm_two_arrs`, its `_const` and `_antisym` variants, `array_init_symmetr_swap`.
- Expression pressure: `array_tripl_access_init`, `array_tiling_pr4`, `array_tiling_pr5`.
- Previous auxiliary cases: `array_hybr_sum`, `array_init_ite_dupl`, `array_two_counters_sum`.

Configurations, introduced in order:

1. Baseline: shadow encoding off, history synthesis off.
2. Shadow encoding on, history synthesis off.
3. Existing nonlocal history with exact-property predicates, shadows off.
4. Repaired repeated-pattern history with the same guard/retention settings, shadows off.

Run diagnostic tests first, then five alternating timed repetitions of configurations 1–2 on the local panel. Evaluate configurations 3–4 on the nonlocal/repetition cases. Expand a promising configuration to the 49-benchmark historical cohort and then all 189, including errors/timeouts and simple controls. Repeat noisy or near-threshold comparisons; do not infer a win from one run.

Measure total runtime, solver time, refinements, unique retained schemas, indexed assertions, generated shadow count, and construction/interpolation cost. Report accepted candidate coverage separately from successful completion and runtime wins.

A useful first result is several nontrivial benchmarks with at least 15% median runtime improvement, accompanied by reduced refinement/solver work and no new incorrect answers. Treat a >20% slowdown on a nontrivial case as a reason to narrow eligibility before broader rollout. Always include failures/timeouts in the outcome comparison; do not report only shared successes.

## Deferred work and separate estimates

- **Install shadows only after online repetition:** approximately 700–1,200 additional lines including tests. Requires a coherent strategy for all past frames, property rewriting, term catalogs, and solver reconstruction or equivalent retroactive constraints. Decide after the startup encoding demonstrates value.
- **Capture arbitrary scalar expressions or read values:** approximately 500–800 additional lines including tests. `HistorySpec` accepts a term, but current candidate selection/localization only supports one declared scalar at the latest frame. Extending that restriction and validation is the real work.
- **Fixed-delay histories or phase snapshots:** no commitment based on the observed frame gaps. First identify a proven transition recurrence or capture event; design and estimate that narrower transformation from a concrete example.
- **Relational summaries across shadows:** defer until ordinary paired shadows show that relational reasoning remains expensive. Maintaining two shadows at the same index is already included above.

The first implementation should end with a measured decision about stable property-index shadows and a separately measured repetition policy. The benchmark coverage estimates select experiments; they do not establish that 26% of the suite will improve.
