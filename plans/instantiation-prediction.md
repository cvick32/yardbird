# Predicting instantiations across BMC depths

Status: implementation proposal, 2026-09-10. This document plans the feature;
the integrated predictor has not been implemented or benchmarked.

## Objective and first milestone

At each new BMC depth, instantiate selected temporal patterns learned from
ordinary refinement at earlier depths. If the existing property check returns
UNSAT, advance immediately. If it returns SAT, run ordinary CEGAR against the
resulting model and learn from the instances it actually discovers.

The first milestone is an opt-in `predictive-full-unroll` instantiation policy
that demonstrates a measured end-to-end improvement on German with 40 winners
and assumption-based property checks. Preserve the existing default policy,
candidate ranking, cost functions, and counterexample validation.

The predictor guesses **which valid theory instances will be useful**, not
which formulas are true. Every emitted instance must be reconstructed from a
supported theory rule and a well-typed substitution. Similar-looking formula
text alone is insufficient authorization to assert a lemma.

## Evidence and limits of the replay

The primary experiment used:

```sh
cargo run --release -- \
  -f examples/distributed_protocols/german/german.vmt \
  --candidate-winners-per-group 40 \
  --property-check-mode assumptions \
  -d 20
```

The capture contained 56 solver checks, 241 distinct relative instance schemas,
and 3,933 indexed assertions. Its profiled driver took 45.03 seconds, including
18.07 seconds of raw solver checking and 26.70 seconds of refinement generation
and installation. Depth 20 means the experiment visits depths 0 through 19.

Replay prediction began at depth 15. A conservative family needed two distinct
previously discovered frame gaps; a broad family needed one. Both preserved
symbol identity, operators, constants, frame equality, and temporal order.

| Replay mode | Median measured solver time | Prediction allowance | Estimated end-to-end cost | Checks | Added predicted assertions |
|---|---:|---:|---:|---:|---:|
| Original | 17.81 s | 0 | 44.51 s | 56 | 0 |
| Batch-only hindsight control | 14.06 s | 0 | 40.77 s | 42 | 0 |
| Two-gap prediction | 16.63 s | 2.50 s | 28.74 s | 39 | 4,373 |
| One-gap prediction | 25.72 s | 2.50 s | 37.84 s | 39 | 13,295 |

These are medians from three repetitions per mode. Estimated end-to-end cost
adds measured replay time, 0.5 seconds per prediction call, and the original
generation cost at depths whose refinement was retained.

Both predictors needed fallback at depth 16 and immediately discharged depths
17, 18, and 19. Depth 15 was already immediately UNSAT in the original capture;
it is not an avoided-refinement success. The avoided original generation and
installation at depths 17–19 totaled 17.09 seconds.

The conservative estimate is a 35.4% reduction, or about 1.55× speedup. This is
the motivation for implementation, **not a measured integrated speedup**:

- Replay fallback appended recorded future instances in a batch. A live
  predictor has to discover fallback instances from its changed solver model.
- The estimate assumes the retained discovery work costs approximately what it
  did in the original run. That assumption remains untested.
- With the allowance, conservative solver cost alone rose from 17.81 to
  19.13 seconds. Avoiding generation is the main proposed benefit.
- More aggressive prediction tripled the added assertions without avoiding
  additional refinement depths. Start with the two-gap rule.
- The earlier default-CLI experiment sometimes needed historical instances
  from previously skipped refinement rounds. Live fallback must remain able to
  discover them later; there is no runtime oracle for missing history.
- Depth 15 was an experimental cutoff, not an established optimal warmup.

Detailed local evidence:
[variant report](../.scratch/german-prediction-replay-w40-assumptions/prediction-report.md),
[variant summary](../.scratch/german-prediction-replay-w40-assumptions/prediction-summary.json),
[replay harness](../.scratch/german-prediction-replay-w40-assumptions/replay_predictions.py),
and [default-run report](../.scratch/german-prediction-replay/report.md).
These artifacts are in ignored scratch directories. Implementation should
retain a small, versioned fixture and experiment manifest; the links alone are
not a portable regression suite.

The captures used Z3 4.16.0. The source revision was
`eee55e824024a2b568fd42656cbc83071d4a0a25` with existing working-tree changes;
the revision alone does not reproduce that source state. The captured binary
SHA-256 was
`e87ae26b9b9687de693adc11b71c803020d596c92a9f3a9cc05045c6c7e1b584`.

## Scope and configuration

Add `PredictiveFullUnroll` to `InstantiationStrategyType`. Its baseline
behavior is ordinary full unrolling, augmented with bounded prediction before
the first property check at each eligible depth.

Initial supported configuration:

- VMT input, abstract array strategy, Z3 backend.
- Both scoped and assumption-based property checks.
- Existing cost functions and winner counts remain independent options.
- Built-in array axioms and certified positive universal-binder instances.
- Exactly two distinct temporal frame classes in an eligible substitution.
- A fixed model, variable registry, and rule registry for the session.

Explicitly reject unsupported combinations at configuration validation:
SMTLIB mode, list/BV-list theory, concrete or quantified-array strategy,
other solver backends, and dynamic auxiliary synthesis that changes the model
or rule registry. Existing instantiation policies remain separate enum choices.
Extending this matrix is subsequent work, not an implicit fallback to a
different policy.

Proposed initial CLI options:

| Option | Initial default | Meaning |
|---|---:|---|
| `--instantiation-strategy predictive-full-unroll` | Opt-in | Enable this policy |
| `--prediction-start-depth` | 15 | Earliest depth that may emit predictions |
| `--prediction-min-gap-examples` | 2 | Distinct genuinely discovered gaps needed |
| `--prediction-max-assertions-per-depth` | 4096 | Additional solver assertions from prediction, including supporting definitions |
| `--prediction-max-assertions-total` | 20000 | Session-wide additional prediction assertions |

These are provisional experimental defaults, especially the start depth and
caps. Reject prediction-only options when another policy is selected rather
than silently ignoring them. Allow a threshold of one for the documented
ablation; reject zero. A zero assertion budget is a useful disabled-prediction
control and must behave like full unrolling.

Do not add adaptive confidence, demand ranking, model evaluation of predictions,
or extra speculative solver checks in the first version. Those would obscure
whether the replay mechanism works live. This is separate from the existing
[demand-guided ranking plan](demand-guided-instantiation.md).

## What the predictor learns

### A typed family of substitutions

A family key contains:

1. Rule identity and direction: the particular array axiom or registered binder
   instance kind, including array sorts or binder identity.
2. The complete substitution AST, preserving every symbol, literal, operator,
   sort, repeated occurrence, and shared subterm relationship.
3. Two ordered temporal classes, `earlier` and `later`, replacing numerical
   frame offsets. Immutable symbols remain immutable.

For example, these substitutions for read-away-from-write belong to one family:

```text
array=A+0, write_index=i+0, value=v+0, read_index=j+2
array=A+0, write_index=i+0, value=v+0, read_index=j+3
```

They provide gap evidence `{2, 3}`. At depth 4 the family can propose the missing
relative gaps 1 and 4. For gap 4, the rule constructs:

```text
i+0 != j+4  =>  Read(Write(A+0, i+0, v+0), j+4) = Read(A+0, j+4)
```

The inequality guard is part of the rule and must remain. Do not learn only
the equality that happened to be justified by one solver model.

The following are different families: replacing `A` with `B`, swapping which
terms are earlier and later, changing a literal, changing a sort, or changing
which repeated occurrences share a frame. Translating every frame by the same
amount supplies no new gap evidence. Width-zero families and families with
three or more temporal classes are ineligible initially.

### Relative gaps reuse full-unroll placement

Yardbird already normalizes instances to relative frames and installs a schema
of width `g` at frames `g..=depth`. Consequently, one predicted relative schema
for gap `g` covers the ordered frame pairs:

```text
(0, g), (1, g+1), ..., (depth-g, depth)
```

Use that representation rather than introducing a second absolute-frame term
rewriter. A family that becomes eligible late must be able to fill older frame
pairs too; limiting prediction to pairs touching the newest frame would change
the replay experiment. Placement remains bounded as described below.

### Evidence rules

- Observe only candidates actually selected and accepted through ordinary
  refinement, with a supported rule certificate.
- Count distinct gap widths, not the number of ground placements or discoveries
  at different depths. Two distinct gaps may be discovered at the same depth.
- Use only observations from completed earlier depths for the next prediction
  pass. Never invoke prediction midway through refinement at the same depth.
- Predicted instances and their future replays do not increase confidence.
- Ordinary discovery can promote a previously predicted schema and supply
  genuine evidence if it independently passes ordinary candidate selection.
- Store the two witness observations needed for eligibility, distinct observed
  gaps, and bounded diagnostic references. Do not retain whole e-graphs or
  solver models for prediction.

## Architecture and integration points

Keep pattern learning in a small solver-independent module. Keep assertion
placement, materialization, and tracking in the existing installation context.

| Location | Planned responsibility |
|---|---|
| New `src/instantiation_prediction/` | Typed family keys, observation state, gap enumeration, rule reconstruction, bounded prediction requests |
| New `src/instantiation_strategy/predictive_full_unroll.rs` | Once-per-depth orchestration, ordinary replay, prediction budgets, placement coverage |
| `src/instantiation_provenance.rs` | Semantic seed metadata and discovered/predicted origin on requests and stored schemas |
| `src/quantified_rule.rs` | Stable supported-rule identity and certificate construction boundary |
| `src/quantifier_abstraction.rs` | Reconstruct positive universal instances through the registered binder rule |
| `src/strategies/array_abstract.rs` | Preserve rule metadata at `finish`; use the correct inventory for novelty filtering |
| `src/problem_context.rs` | Separate candidate novelty from the inventory used for export; normalize certified bindings with the term |
| `src/instantiation_strategy/mod.rs` | Shared explicit-placement installer, origin-aware storage/promotion, bounded preparation |
| `src/instantiation_strategy/assertion_tracker.rs` | Deduplicate predicted non-equality formulas as well as equality formulas |
| `src/vmt_bmc_session.rs` | Supply typed frame context; run the policy after unroll declarations and before the property check |
| `src/lib.rs` | CLI enum/options, construction, and compatibility validation |
| `src/profiling.rs`, capture/training records | Origin, prediction timings, counters, configuration, compatible serialization |

The prediction module needs only operations equivalent to:

```text
observe(certified ordinary instance, discovery depth)
predict(depth, typed frame context, work budget) -> bounded certified requests
```

Keep coverage and actual assertion accounting with the installation policy.
Prediction does not call Z3, mine trace files, or own the CEGAR loop. Names and
exact Rust signatures can follow existing ownership conventions during
implementation; do not introduce a plugin framework for one predictor.

### Preserve trusted rule information

`Abstract::finish` currently has `candidate.rule`, but installation retains
only the normalized term and substitution provenance. Extend this path to carry
a compact semantic seed independently of optional decision/training logging.
Enabling prediction must not require `--record-decisions` or unsat-core tracking.

For built-in arrays, reconstruct from `ArrayAxiomKind`, the typed signature,
and the complete substitution. For positive universal instances, use the
registered `BinderRule::instantiate` path, preserving helper captures and the
implication from the quantified helper to its body. The helper name alone is
not a certificate, and `QuantifiedRuleKind::Other` is not sufficient evidence
that a candidate is a positive universal instance.

Normalize the complete term and all binding terms together using
`UnquantifiedInstantiator`, the VMT variable registry, and existing definition
frame metadata. Use AST transformations; do not split symbol strings with a
regular expression to infer temporal semantics.

Initially decline seeds with model-private values, unresolved or unregistered
symbols, open binders, unsupported witness/lambda/existential directions,
unsupported transition guards, or hidden definition offsets that cannot be
accounted for exactly. Declining prediction leaves ordinary refinement intact.
If a supported binder's captures or definitions cannot be safely rebuilt, skip
that family and report the reason rather than asserting a guessed formula.

### Separate discovery, storage, and placement coverage

Use shared schema storage tagged with origin, plus explicit placement coverage.
Track at least:

- Whether the schema has been ordinarily discovered or is prediction-only.
- The certified rule and normalized substitution.
- The predicted family and evidence IDs, when applicable.
- Which predicted placements are asserted or equivalent to asserted formulas.
- Whether any placements remain pending because of budgets.

There is an important existing API overlap: `get_instantiations()` is used both
for result export and as a set of already-known candidates. A partially placed
prediction cannot safely appear as a fully covered ordinary schema in the
latter set. Otherwise the normal search may filter out the very instance
needed after prediction returns SAT.

Add an explicit candidate-novelty accessor on `ProblemContext`, with existing
behavior as its default. In the predictive VMT session, exclude prediction-only
schemas from that accessor. Update array candidate selection, binder candidate
selection, and guarded-update novelty checks to use it. Keep all legitimate
installed schemas available to result/proof export, while ground assertion
records describe only placements actually installed.

When ordinary refinement discovers a prediction-only schema:

1. Promote it to discovered even if schema storage already contains it.
2. Install its missing ordinary full-unroll placements without prediction caps.
3. Record the genuine observation for future-depth learning.
4. Preserve actual solver-progress accounting; promotion alone is not an added
   assertion and cannot hide a `NoProgress` condition.

The current `store_new` duplicate early return must not prevent this promotion.
Normal schemas subsequently receive ordinary full-unroll placement regardless
of prediction budgets. Prediction-only schemas receive bounded placement.

### Reuse the installer without duplicating its mechanics

Factor an internal operation for installing a certified schema at specified
eligible frames. Have both ordinary full unrolling and prediction reuse its
materialization, solver declaration, support-definition, deduplication,
tracking-label, provenance, and subterm-registration behavior.

This makes exact placement a deliberate extension of the current installer,
whose comment presently defers it until provenance is available. Do not expose
an unchecked public operation that arbitrary callers can use to assert terms.

Deduplicate after indexing and materialization. Retain existing equality
canonicalization; use exact AST keys for formulas it cannot canonicalize,
including binder implications without equality. Make the extra non-equality
deduplication opt-in for this policy initially, preserving legacy behavior and
statistics when prediction is disabled. All assertion paths in a predictive
session must share this deduplication state.

Register predicted subterms as derived refinement terms, not problem-authored
source sites. Restore all modified BMC builder state, including width, after
placement. Emit every solver assertion through the existing capture-capable
solver interface.

## Depth lifecycle and fallback

For each new depth:

1. Introduce that depth's variables, model axioms, transition relation, and
   property-check context through the existing VMT unroll path.
2. Replay genuinely discovered schemas using ordinary full-unroll behavior.
3. If warmup and budgets permit, place pending prediction-only schemas and
   generate missing gaps from eligible families. Use deterministic ordering.
4. Perform the existing property check exactly once.
5. On UNSAT, use the existing `NextDepth` path. No e-graph construction or
   refinement generation is needed for that depth.
6. On SAT, execute the existing strategy setup/refinement/finish flow. Retain
   the predictions as valid lemmas; they may change the model and discoveries.
7. On UNKNOWN or failure to make progress, preserve existing error/validation
   behavior. Prediction cannot turn either into a proof.

Use `InstantiationStrategy::on_loop` as the orchestration seam after ordinary
unrolling has made the frame available. Confirm its invocation conditions:
`VmtBmcSession::unroll` currently does nothing on repeated calls at the same
depth and calls the policy only when stored instantiations exist. Depth zero
is constructed separately. No evidence means no prediction; tests must ensure
this special case neither loses ordinary setup nor produces repeated passes.

Prediction assertions are permanent theory lemmas, outside the transient
property scope. Preserve the existing scoped push/pop behavior and the exact
assumption literal in assumptions mode. Do not replace one property-check mode
with the other or add an extra baseline check to decide whether prediction
was necessary.

There is no special live “append the rest of the recorded depth” operation.
Fallback is ordinary discovery, including rediscovery of a useful schema whose
original refinement round was skipped at an earlier depth.

## Work and memory budgets

An assertion cap alone is insufficient: repeated duplicate generation can
consume time while adding nothing. Bound all of the following:

- New prediction assertions per depth and per session, counting supporting
  definitions as well as indexed theory instances.
- Placement attempts per depth, initially 16,384 including duplicates and
  deferred replays. Record cap exhaustion explicitly.
- Families retained, initially 2,048, and term size/work examined while building
  or reconstructing families. Choose the AST work limit from the fixture size
  distribution before wiring the live policy.
- Pending placement metadata. Use compact per-schema frame coverage/cursors
  rather than eagerly allocating the entire future Cartesian product.

Enumerate relative gaps lazily, cache family keys at observation time, and
avoid rescanning the whole stored inventory for each proposal. Interleave
families in a stable order so one family cannot exhaust every depth's budget.
Within a family, use a documented stable gap/frame order; compare that order
with replay because assertion order can affect solver behavior.

Previously predicted schemas are not exempt from future-depth budgets. Replaying
them can create new assertions even when no new family or gap is learned.
After the session cap, stop new predictive placement but continue ordinary
full unrolling and normal refinement. Retain already asserted valid lemmas.

Prepare a complete placement and its required definitions before admitting it
against the remaining budget. Commit it through the shared installer as one
unit. Do not leave an unsupported or partially defined formula in solver state;
do not silently exceed the cap to install its dependencies. If preparation
cannot currently be separated from mutation, make that separation explicit in
the installer refactor or decline that prediction form in the initial version.

Treat 0.5 seconds per prediction call as a performance target to measure, not
a correctness assumption or guaranteed interruptible deadline. Measure family
construction, placement preparation, assertion submission, and solver checks
separately. Prefer deterministic work limits initially; a wall-time emergency
cutoff can be added later if measured outliers justify its nondeterminism.

## Observability and evidence accounting

Add a per-depth prediction record with:

- Enabled configuration; observed, eligible, skipped, and capped family counts.
- Distinct genuine gap observations, generated schemas, and promoted schemas.
- Placement attempts, unique indexed/support assertions, duplicate assertions,
  pending placements, and the reason a budget stopped the pass.
- Time spent observing/normalizing, predicting, preparing, and asserting.
- Whether the following first property check returned UNSAT, SAT, or UNKNOWN;
  whether ordinary refinement ran afterward and how many rounds it took.

Separate discovered schema counts, predicted schema counts, and actual ground
assertions. Tag predicted tracking records with family and evidence IDs so an
UNSAT core can refer back to what generated an assertion. Predictions remain
valid proof inputs; they must not be mislabeled as ordinary ranker selections
or automatically become positive training examples.

Keep profiling JSON backward-readable using optional/defaulted fields and
preserve existing metric meanings. Captured SMT2 must include every predicted
assertion before the correct check, with matching capture-index boundaries.

A live first-check UNSAT is observable; “this prediction avoided refinement”
is a counterfactual comparison. Report the former per run and establish the
latter only by comparing against the matching baseline. Do not credit every
first-check UNSAT as a prediction success.

## Implementation sequence and acceptance checks

### 1. Preserve the experiment and define the contract

- Extract small, versioned representative schemas from the capture: two-gap
  array families, a positive universal family, unsupported witnesses, and
  structurally similar but distinct families.
- Include expected normalized families and gap sets, evidence cutoff depths,
  and a minimal placement fixture. Record the source/configuration/Z3 manifest.
- Fix the supported-rule matrix and assertion/work-budget semantics above.
- Add a small offline adapter for comparing future predictor output to the
  existing Python family construction on a frozen genuine-observation prefix.

Acceptance: the fixture explains exactly what counts as evidence, which gaps
are predicted at a selected depth, and which formulas must never be guessed.

### 2. Carry certified seeds through ordinary installation

- Preserve rule identity and instance direction from selected candidates.
- Normalize rule bindings and formulas together, independent of verbose logs.
- Reconstruct array and positive universal instances through trusted rule code.
- Reject unsupported seed forms with counters and unchanged ordinary behavior.

Acceptance: reconstructed seed formulas match the selected originals modulo
existing safe normalization; metadata does not alter assertions with the new
policy disabled.

### 3. Implement and test the pure family learner

- Implement typed AST family keys and genuine-gap evidence tracking.
- Implement bounded, deterministic enumeration of missing relative gaps.
- Keep future-depth observations, predicted instances, and translated copies
  from contributing false evidence.
- Reconstruct every proposed schema through its certified rule.

Acceptance: fixtures match the conservative replay's family/gap semantics before
budget truncation. Document legitimate differences caused by declining a rule
or helper form instead of hiding them in aggregate counts.

### 4. Make installation origin- and coverage-aware

- Add origins, shared explicit placement, and placement coverage.
- Implement prediction-only storage, promotion, and ordinary missing-placement
  installation.
- Split candidate novelty from export inventory at all relevant consumers.
- Add policy-scoped exact deduplication for non-equality assertions.
- Account for helper definitions and preserve source/derived provenance.

Acceptance: capping a prediction never prevents ordinary refinement from
installing a needed placement. Ordinary policy output remains unchanged.

### 5. Wire the live policy and CLI

- Add configuration validation, strategy construction, and once-per-depth hook.
- Keep the driver SAT/UNSAT/fallback paths intact.
- Include ordinary replay before prediction and charge prediction-only replay
  against the same limits as new predictions.
- Add profiling and capture origin/timing records alongside this integration.

Acceptance: a small end-to-end example reaches the next depth on predicted
UNSAT; another returns SAT and completes through ordinary CEGAR. Both property
check modes work, and real counterexamples remain detectable.

### 6. Measure live performance and decide rollout

- Run the controlled benchmark matrix below with actual fallback discovery.
- Compare against the recorded replay, explaining rule coverage and assertion
  ordering differences before tuning budgets or warmup.
- Save raw runs, configuration, source/binary hashes, and a results report.
- Document the option and limitations in README only after the implementation
  and measurements exist. Keep it opt-in through initial rollout.

Acceptance: correctness and capture checks pass; actual end-to-end results,
including unsuccessful fallback costs, determine whether to retain or revise
the policy. No oracle generation-cost estimate substitutes for this milestone.

## Verification

Use module tests for the learner and a new
`tests/instantiation_prediction_tests.rs` integration suite. Extend existing
quantifier, solver capture, profiling, and counterexample tests where they
already exercise the relevant boundary.

| Area | Required cases |
|---|---|
| Family identity | Uniform translations collapse; different gaps share a family; changed symbol/sort/literal/polarity/temporal order do not |
| Evidence | Two actual gap widths qualify; repeated placements do not; predictions do not teach themselves; current/future depth observations are unavailable |
| Rule validity | Array read/write guards survive; binder captures and implication direction survive; unsupported directions and model values are rejected |
| Frame handling | No negative/future references; width and placement bounds; immutable symbols; quoted symbols; definition offsets; builder state restoration |
| Placement | All eligible older pairs can be filled; new depths extend existing gaps; exact and equality-oriented duplicates are suppressed |
| Budget exhaustion | Work and assertion caps include replays and support; no partial support installation; zero budget reproduces full unrolling |
| Promotion | Partially placed predictions are discoverable; normal discovery fills missing placements without prediction caps; no false progress from metadata alone |
| Lifecycle | One prediction pass per depth; immediate UNSAT skips generation; SAT resumes normal discovery; skipped historical needs can be discovered later |
| Solver scope | Scoped and assumptions modes retain their intended property checks; predictions persist outside property scopes |
| Artifacts | Predicted assertions appear in SMT2, tracking, and proof records; old JSON still loads; candidate training labels retain their meaning |
| Outcomes | Compare bounded results with baseline/concrete checks on small supported cases; real counterexamples and UNKNOWN remain correctly handled |

For rule-validity tests, check generated instances against native array
semantics or the defining quantified binder semantics on small formulas. These
are theory lemmas; they need not follow from the deliberately weakened abstract
solver assertions alone. Keep syntactic family tests separate from semantic
validity checks.

Avoid flaky unit assertions about wall time. Test bounded work deterministically
and measure timing in release-mode experiments. Run focused tests during each
phase, then `cargo test` and the repository's applicable formatting/lint checks
before handing off the implementation. Establish pre-existing failures before
attributing a failure to this feature; the source already has unrelated edits.

## Live benchmark protocol

Build once in release mode, then time the binary directly to exclude Cargo
build time. Use identical source, solver version, machine settings, depth, and
all non-prediction options for each paired comparison. Run solvers serially;
interleave/randomize baseline and predictor order across at least five
repetitions. Preserve all failures and timeouts in the report.

Primary comparison:

```sh
# Baseline
target/release/yardbird \
  -f examples/distributed_protocols/german/german.vmt \
  --candidate-winners-per-group 40 \
  --property-check-mode assumptions -d 20

# Proposed live predictor
target/release/yardbird \
  -f examples/distributed_protocols/german/german.vmt \
  --candidate-winners-per-group 40 \
  --property-check-mode assumptions -d 20 \
  --instantiation-strategy predictive-full-unroll \
  --prediction-start-depth 15 \
  --prediction-min-gap-examples 2
```

Use capture-free, consistently instrumented runs for the primary wall-time
comparison. Collect separate `--solver-capture-dir` diagnostic runs to verify
replay and explain per-depth behavior; do not compare a captured baseline to an
uncaptured predictor. Measure lightweight predictor observation overhead during
warmup too, not only the prediction calls after depth 15.

Report medians, ranges, and paired changes for wall time, raw solver checks,
ordinary generation/installation, prediction construction/installation, check
counts, refinement rounds, schema/assertion counts, and peak memory when
available. Every end-to-end total is measured live; no 0.5-second substitution
or retained-original-generation proxy is used in the implementation result.

Run these comparisons in order:

1. Primary German configuration: full-unroll, zero-budget predictor control,
   conservative predictor with replay-matching warmup.
2. German with the default winner count and scoped checks. This tests the trace
   that previously needed skipped-history recovery.
3. Array-only versus array-plus-certified-universal prediction, to identify
   whether binder support is needed for the observed gain.
4. Targeted warmup and budget ablations after the baseline comparison: start at
   eligibility versus fixed depths such as 10 and 15; smaller assertion caps;
   threshold one only as a bounded diagnostic.
5. A broader cohort: other distributed protocols including Tomasulo, selected
   array split/tiling/nonlinear examples from the demand-guided benchmark
   cohort, and small cases with real counterexamples. Select actual supported
   files from the repository and record the list before measuring.

Do not expect precisely 39 checks or 4,373 added assertions in the integrated
run. Live fallback discovers from changed models, certified-rule filtering may
exclude replay families, and relative-schema placement may change assertion
order. Use frozen-prefix parity tests to distinguish implementation errors
from legitimate live divergence.

Proposed decision criteria:

- Mandatory: sound rule construction, matching verification outcomes on the
  supported test cohort, intact fallback, and complete replayable captures.
- Primary performance target: at least a 20% median end-to-end reduction on
  the 40-winner German configuration over five repetitions, without introducing
  timeouts or counterexample regressions. This is a proposed engineering target,
  not an experimental result.
- Overhead target: prediction construction and bookkeeping below 0.5 seconds
  per call on the primary case; report assertion submission separately and
  include both in total wall time. Also report warmup observation overhead.
- Default-off overhead: no prediction state, work, or assertion-order changes
  when the policy is not selected, apart from tested shared metadata plumbing.
- Keep the policy opt-in if gains depend strongly on configuration. Consider
  enabling it more broadly only after the separate cohort shows acceptable
  runtime and memory behavior.

If early UNSAT disappears under live fallback, first inspect the family/rule
coverage and the actual depth-16 discoveries. If the same useful lemmas are
present but solver time dominates, investigate assertion volume/order. If
prediction rarely avoids generation, focus subsequent work on selecting or
generating better instances. Do not respond to a failed benchmark by silently
adding hindsight information or expanding into a general learning system.

## Completion checklist

- [ ] Typed, certified two-frame family learning is implemented and tested.
- [ ] Only actual earlier discoveries establish prediction eligibility.
- [ ] Prediction-only storage, bounded placement, promotion, and novelty
      filtering cannot block ordinary CEGAR.
- [ ] Array and positive universal instances retain their full rule semantics.
- [ ] New policy is opt-in, validated, and compatible with both property modes.
- [ ] Actual assertions and timings are visible in capture/profiling records.
- [ ] Live German results replace the replay projection with measured totals.
- [ ] Counterexamples, later historical needs, and budget exhaustion are tested.
- [ ] Broader benchmark results and remaining limitations are documented.
- [ ] Existing defaults and unrelated working-tree changes are preserved.
