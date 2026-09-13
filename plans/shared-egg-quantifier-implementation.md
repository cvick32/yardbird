# Shared egg quantifier implementation results

Implementation and validation completed 2026-09-12 against HEAD
`eee55e824024a2b568fd42656cbc83071d4a0a25`, extending the incoming uncommitted
shared-engine patch. See [the review](shared-egg-quantifier-review.md) for the
original findings and scope. No files were staged or committed.

Follow-up: the user accepted the documented benchmark failures. A subsequent
correctness review found no logical correctness blocker and identified two
profiling defects, now fixed: matching and grounding have separate timers, and
continuable pages are distinct from exhausted budgets. The cleanup passed 254
library tests, 6 quantified-rule characterization tests, 4 solver-profiling
tests, Clippy with warnings denied, formatting, and whitespace checks. Its
regression logs and source hashes are under
`.scratch/unified-quantifier-implementation/profiling-cleanup/`. The results
below remain the historical implementation/benchmark record; these profiling
changes do not alter search or selection behavior.

## Outcome

The model-first shared engine and search-coverage fixes are implemented. The
default protocol validation gate remains open: Chord exceeds 250 refinements,
and several protocol workloads remain slower than HEAD. The patch is suitable
for further evaluation, but should not be described as a fully validated
replacement yet. Raising the configured budget demonstrates a useful operating
point; it does not resolve the default-policy regression.

## Changes

- Added `src/theories/array/quantified_search.rs` to separate raw egg matching
  from representative extraction. Array rules retain their historical backoff
  range instead of silently stopping at 4,096 substitutions. Candidate batches
  expose incomplete rules and examined substitution counts.
- Binder searches use 4,096-substitution pages, with real lookahead and an
  accounted continuation offset. If a page has no selectable candidate, the
  caller continues past its satisfied or known prefix. Each rule is limited to
  65,536 substitutions per search pass. Since egg cannot resume its join,
  repeated prefix work is bounded too: at most 16 queries and 557,072 returned
  substitutions, including lookahead. This is a substitution bound, not a
  wall-clock bound. Reaching it reports incompleteness, never a proof or a
  satisfiability result.
- `QuantifierPlan` caches compiled rules by array types. Each SAT model gets one
  `PreparedQuantifierSearch`, containing its typed e-graph, original cheap
  representatives, model-value cache, and obligation cache. Phases and array
  stages reuse that context; a new solver check gets a new context. A later
  stage can restart matching with changed selection history while reusing model
  facts.
- Conflict phases now follow `match -> cheap obligation -> model filter ->
  ranked extraction -> complete-instance scoring -> novelty and group ranking`.
  Satisfied matches do not construct the configured cost function or invoke
  ranked extraction. Surviving matches use the existing shared grounder,
  contextual selector, cost function, ranker, and decision history. Ranked term
  pools are restricted to surviving binding classes; fallback extraction visits
  their dependency closure, preserving representative choices without scoring
  unrelated classes.
- Fresh, capture-dependent witness functions and polarity are preserved.
  Expansion still accepts satisfied instances that can expose nested helpers,
  including witness obligations. The original term-admission policy remains in
  force; cheap evaluation representatives are not automatically admitted to the
  optimized candidate vocabulary.
- Separated equality-conflict handling from grouping, removed fake duplicate
  binder trigger/consequence fields, and renamed the internal `Other` category
  to `InputBinder`. Current phase priority and grouping remain unchanged; source
  occurrence budgets and a global selector remain deferred.
- Added model-preparation, obligation-cache, filtered-match, search-work, and
  per-phase profiling. Updated README to describe the actual search limits,
  caching, expansion exception, and binder-budget behavior.

## Verification

The permanent 4,097-array-conflict regression was first observed failing with
only 4,096 results, then passed after the fix. New tests cover zero cost-factory
and scoring calls for rejected matches; selective fallback costs; model-value
preservation after extraction; shared obligation caches; history changes;
4,225-match continuation with its only violation after the first page; actual
65,536-window exhaustion against 66,049 matches; compilation invalidation;
satisfied expansion; and one graph preparation per SAT model on a nested binder
fixture.

| Check | Result |
| --- | --- |
| Release library suite | 252 passed |
| Seven affected integration suites | 41 passed |
| `cargo clippy --offline --all-targets -- -D warnings` | Passed |
| `cargo fmt --all -- --check` and `git diff --check` | Passed |
| Distributed protocol suite, serial | 4 test groups passed; 3 failed |
| Array-only comparisons | Same outcomes on HEAD and final binary |

The seven integration suites are quantified-rule characterization, round-robin
grounding, source-write parsing, guarded read updates, solver capture, solver
profiling, and concrete-counterexample fallback. Existing polarity/alternation
and quantifier-free solver tests remain enabled. No protocol timeout or
refinement limit was relaxed and no test was skipped.

Array-only comparisons used array-copy and array-split at depth 5 and the buggy
array-copy example at depth 3. Copy completed with 7 steps/10 instances on both
binaries; split completed with 5 steps/0 instances; both binaries reported the
buggy copy's counterexample. These are correctness smoke checks, not repeated
performance measurements.

## Serial performance measurements

Three paired release runs per case, alternating execution order, with no solver
captures or profiling and no concurrent build/test jobs from this task. Wall
times varied on the shared host; all per-case refinement/instance counts were
stable across the three runs. Do not infer exact speedup factors from one run.

| Case | HEAD median (range), seconds | Final median (range), seconds | Steps, HEAD -> final | Instances, HEAD -> final |
| --- | --- | --- | --- | --- |
| Database depth 2, default budget 1 | 13.16 (10.93–17.94) | 28.21 (20.96–28.82) | 44 -> 231 | 2,259 -> 1,012 |
| Database depth 2, budget 40 | 16.72 (14.49–17.20) | 10.82 (10.43–10.89) | 31 -> 29 | 2,705 -> 906 |
| German depth 20, budget 40, assumptions | 37.77 (35.95–47.00) | 51.23 (50.71–55.47) | 45 -> 56 | 3,490 -> 3,933 |
| Two-phase commit depth 5, default budget | 0.962 (0.909–1.265) | 1.264 (1.141–1.831) | 25 -> 31 | 167 -> 147 |

All 24 runs completed successfully. Database defaults reliably fit the existing
60-second test timeout, but the runtime regression versus HEAD remains. The
old path bypassed the binder winner budget; the shared path honors it. Fewer
installed instances now require many more solver/refinement cycles at budget 1.
German's regression shows that budget enforcement alone does not explain every
workload. Selection and representative effects need further investigation.

A separate final database run with profiling, tracking, and solver capture
completed in 17.84 seconds, with 229 steps and 1,014 instances. Its counts differ
from the capture-free cohort; do not combine their timings. It recorded:

- 227 binder preparations for exactly 227 SAT models.
- 112,477 satisfied matches rejected before ranked grounding; 50,981 binder
  matches sent to grounding; 50,640 obligation-cache hits.
- 1.44 seconds of preparation, 0.75 seconds of binder matching, 4.60 seconds of
  cheap obligation filtering, and 1.35 seconds of extractor initialization.
- 0.023 seconds in complete-instance cost calls and 0.042 seconds in solver
  checks. These narrow counters exclude surrounding construction/selection.
- 38,514 duplicate or uninstallable formulas filtered and no truncated search.

Timing counters include nested scopes and must not be summed indiscriminately.
In these historical captures, `rule_search_total` measures grounding after raw
matching; `input_binder_matching` and per-rule search records measure matching.
The subsequent profiling cleanup replaces the ambiguous timer with
`rule_matching_total` and `rule_grounding_total`, and separates available next
pages from budget exhaustion in reports and counters. The binary hashes and
measurements below describe the pre-cleanup binary. Continued
optimization should focus on model-obligation work and repeated novel-candidate
discovery across many refinements, rather than the scalar cost function itself.

## Remaining protocol gate

| Failure | Attribution |
| --- | --- |
| Tomasulo depth 2 exceeds 60 seconds | Also recorded on retained HEAD baseline |
| Synchronous lock server exhausts at depth 4 | Also recorded on retained HEAD baseline |
| Chord initial state exceeds 250 refinements | Shared-engine regression versus HEAD; also failed on incoming patch |

The Chord diagnostic is decisive about attribution: HEAD completed its initial
state in 21.74 seconds with 41 steps/3,174 instances under profiling/capture;
the saved incoming shared-engine binary timed out at 60 seconds. The final
protocol suite hits the refinement limit. A separate final run with budget 40
completes in 2.58 seconds with 21 steps/604 instances. That supports investigating
batch selection, but it does not justify silently changing the default or
claiming the default test passes. The inventory test stops at Chord, so its
later cases have not all been freshly validated by that test run.

Before accepting the complete replacement, fix or explicitly settle the
default batching policy using Chord and the default database cohort as gates,
then repeat the same serial comparisons. Keep dependent witness construction,
nested-helper discovery, and quantified exhaustion semantics intact. No global
selector or source-occurrence budget redesign has been introduced here.

## Reproduction artifacts

All fresh logs, exact commands, binary hashes, and machine-readable results are
under `.scratch/unified-quantifier-implementation/`:

- `final-tests.log`, `protocol-tests.log`, `clippy-final.log`, `cap-red.log`.
- `benchmark.py`, `benchmark-results.json`, and per-run JSON/log files.
- `array-smoke.py`, `array-smoke-results.json`.
- `final-diagnostic.json`, `final-profile-summary.json`, and
  `database-final-profile-after-0-capture/`.
- `chord-diagnosis.json`, `chord-w40-result.json`, and associated outputs.
- `final-manifest.json`, including changed source hashes and Cargo.lock hash.

HEAD binary SHA-256:
`caea346043410297bb7eef31d032235ac309366941daa857e2e16a20e0807d9f`.
Final binary SHA-256:
`c626246012595de363d74c196de7b177c0a1b9eb18b553a3376df4092f56ecb9`.
Earlier intermediate benchmark artifacts are retained separately and are not
the measurements reported above. The older default diagnostic label collided
with an existing capture manifest and was rerun under the fresh
`database-final-profile` label; that artifact-write error is not a solver result.

Baseline attribution for Tomasulo and lock server is retained evidence in
`.scratch/unified-quantifier-instantiation/baseline-results.json`, rather than a
fresh rerun in this implementation pass. Production sources for the retained
HEAD binary were checked against the archived HEAD tree during review.
