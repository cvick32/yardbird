# Abstract vs. concrete array reasoning in Z3

Date: 2026-08-05

Evaluation: `full-instrumented-z3`

Status: research note; no code changes

## Bottom line

The experiment supports a narrower conclusion than either "abstraction wins" or
"Z3 ignores useless array lemmas":

1. **Abstraction removes most direct native-array callback time.** On the 175
   benchmarks solved by both strategies, the median paired abstract/concrete
   array-envelope ratio is 0.087; abstraction has the lower envelope in 171 of
   175 pairs. The median envelope is 0.054 ms for abstract and 0.413 ms for
   concrete.[^replay]
2. **That saving does not reliably reduce total Z3 time.** The median paired
   abstract/concrete ratio is 1.149 for stock external replay time (abstract is
   faster in 48 pairs and slower in 127) and 1.256 for instrumented internal
   check time (41 faster, 134 slower). The abstract non-array residual is higher
   in 145 pairs, with a median ratio of 1.507.[^replay]
3. **The conflict counts are of the same order, but abstract is not lower.** Of
   173 pairs with a reported nonzero count, 60 are within 10% and 98 are within
   25%. The median is 136 abstract versus 105 concrete, and the median paired
   abstract/concrete ratio is 1.165.[^raw]
4. **Two tail cases determine the aggregate result.** `array_tiling_pnr3` and
   `array_tiling_pnr4` account for 900,245 of 974,309 abstract conflicts and
   66.167 of 68.169 seconds of instrumented internal time. Removing just those
   two reverses the totals: abstract/concrete becomes 74,064/129,404 conflicts
   and 2.002/3.816 seconds of internal time.[^raw][^replay]
5. **Demand-guided ranking remains promising for Yardbird overhead, but reducing
   checks alone is not enough to reduce Z3 time.** The successful abstract runs issue
   419 intermediate SAT checks, yet those checks account for only 2,086
   conflicts and about 143 ms of instrumented internal time. Almost all abstract
   conflicts occur in the 1,750 final UNSAT checks. A successful selector must
   prefer formulas that also make those later UNSAT checks cheaper, not merely
   remove SAT round-trips.[^captures]

The most useful research target is therefore not the suite-wide median. It is
the sharp scaling transition in `array_tiling_pnr2/3/4`, where the same abstract
scheme goes from a large win to a catastrophic loss as explicit instances and
generic EUF/BCP work accumulate.

## Method

The run contains 189 depth-10 array benchmarks, the concrete Z3 array theory,
and the abstract BMC-cost strategy. Each benchmark used a 20-second timeout and
fixed random seeds. Concrete completed all 189; abstract completed 175 and
timed out on 14.[^run][^config]

The main comparisons below use only the **175 matched successful pairs**. This
avoids the workbook's unpaired strategy medians (175 abstract sessions versus
189 concrete sessions), but necessarily gives abstraction favorable survivorship
bias because its 14 timeouts have no completed capture.[^workbook][^report-aggregation]

Three timing boundaries are kept separate:

- Yardbird's `solver_time` is the accumulated duration of its in-process Z3
  `check()` calls. The timer is recorded before model acquisition
  ([`src/solver/z3.rs:145-172`](../src/solver/z3.rs#L145-L172)).
- Stock replay time is the pipe round-trip from sending each `check-sat` until
  its result arrives, summed over the full incremental session. Each session is
  the median of 15 repetitions after 3 warmups, with stock and instrumented run
  order alternated
  ([`tools/z3_profile/comparison.py:120-178`](../tools/z3_profile/comparison.py#L120-L178),
  [`tools/z3_profile/runner.py:177-211`](../tools/z3_profile/runner.py#L177-L211)).
- Instrumented internal time covers Z3's check boundary. Its array envelope is
  an inclusive outermost timer around array-theory callbacks; later SAT/EUF work
  caused by an array consequence and array work while assertions are installed
  between checks are excluded
  ([`plans/z3-instrumentation.org:212-250`](../plans/z3-instrumentation.org#L212-L250),
  [`plans/z3-instrumentation.org:964-970`](../plans/z3-instrumentation.org#L964-L970)).

The build was Z3 4.16.0, revision
`ddb49568d3520e99799e364fb22f35fc67d887b1`, compiled with `-O3 -DNDEBUG`.[^builder]

## Quantitative findings

### Paired central tendency

All values are medians over the 175 matched pairs unless stated otherwise.
Absent zero-valued Z3 statistics are treated as zero; `conflicts` is available
for 173 pairs.[^raw][^replay]

| Metric | Abstract | Concrete | Median paired A/C ratio |
|---|---:|---:|---:|
| Checks | 12 | 10 | 1.20 |
| Conflicts | 136 | 105 | 1.165 |
| Decisions | 489 | 309 | 1.50 |
| Clause propagations | 2,178 | 1,158 | 1.46 |
| Binary propagations | 1,254 | 228 | 2.36 |
| Added equality attempts | 2,714 | 1,568 | 1.56 |
| Resource-limit count | 46,130 | 20,331 | 1.68 |
| Boolean variables created | 984 | 1,321 | 0.92 |
| Clauses created | 662 | 1,235 | 0.60 |
| Yardbird/native "instantiations" | 40 | 162 | not comparable |
| One-shot in-process `solver_time` | 5.499 ms | 6.214 ms | 0.81 |
| Stock session replay | 14.820 ms | 9.910 ms | 1.149 |
| Instrumented internal check time | 6.436 ms | 4.039 ms | 1.256 |
| Array callback envelope | 0.054 ms | 0.413 ms | 0.087 |
| Non-array residual | 6.400 ms | 3.565 ms | 1.507 |
| Array share of internal time | 0.85% | 15.12% | - |

The abstract encoding creates fewer Boolean variables and clauses, but it asks
the generic solver to do more branching, BCP, equality processing, interface
work, and final checking. In the paired raw totals, abstract/concrete has
6.72M/1.91M binary propagations, 7,337/428 interface equalities, and
12,068/881 final checks.[^raw] This is evidence that explicit guarded UF lemmas
move work into generic CDCL(T)/EUF rather than simply removing array work.

The paired runtime difference tracks that generic work much better than it
tracks native array work. Spearman correlations with the log internal-time
ratio are 0.629 for the resource-count ratio, 0.583 for added equalities, 0.549
for decisions, 0.526 for conflicts, and 0.430 for clause propagations. They are
only 0.094 for concrete's array-time share, -0.053 for the array-envelope ratio,
and -0.031 for the concrete native-instantiation proxy.[^raw][^replay]

This is also visible when the pairs are split by outcome. In the 41 benchmarks
where abstract internal time is lower, the median conflict ratio is 0.983 and
the median added-equality ratio is 0.902. In the 134 losses they rise to 1.234
and 1.755. Median internal time per conflict is nevertheless similar—40.0 µs
abstract versus 37.6 µs concrete—so the common `conflicts` counter is acting
as a rough search-volume marker, not revealing the provenance or usefulness of
array consequences.[^raw][^replay]

The one-shot in-process timing points in the opposite direction from repeated
replay. These are not the same execution boundary: replay goes through the
SMT-LIB shell and may charge pending setup/parsing work to a later `check-sat`,
whereas Yardbird uses the C API. The instrumentation plan explicitly warns that
SMT-LIB replay is not identical to C-API execution
([`plans/z3-instrumentation.org:949-954`](../plans/z3-instrumentation.org#L949-L954)).
This disagreement is a reason to add repeated in-process C-API instrumentation,
not to select whichever number favors one strategy.

### The `tiling_pnr` phase transition

| Benchmark | Checks A/C | Explicit A inst. | Conflicts A/C | Internal time A/C | Concrete array envelope |
|---|---:|---:|---:|---:|---:|
| `array_tiling_pnr2` | 17 / 10 | 110 | 15,179 / 38,660 | 0.107 / 0.366 s | 0.050 s |
| `array_tiling_pnr3` | 18 / 10 | 244 | 348,040 / 196,022 | 3.350 / 1.876 s | 0.200 s |
| `array_tiling_pnr4` | 25 / 10 | 561 | 552,205 / 288,549 | 62.816 / 7.630 s | 0.590 s |

`pnr2` validates the abstraction thesis: it avoids enough array-caused and
generic work to win. By `pnr3` and especially `pnr4`, explicit instantiation no
longer propagates efficiently enough; the abstract residual, not the native
array envelope, explodes.[^raw][^replay] This family should be the first scaling
microbenchmark for demand-guided ranking, frame placement, and propagation
changes.

The three largest stock-replay abstraction wins show the same positive regime:

| Benchmark | Stock replay A/C | Conflicts A/C | Concrete array envelope |
|---|---:|---:|---:|
| `array_tiling_skipped` | 0.160 / 1.323 s | 12,077 / 35,725 | 0.326 s |
| `array_two_counters_replace` | 0.123 / 0.771 s | 7,572 / 20,861 | 0.171 s |
| `array_tiling_pnr2` | 0.114 / 0.360 s | 15,179 / 38,660 | 0.050 s |

Here abstraction reduces both direct array work and the downstream search. That
is the behavior to reproduce at `pnr3/4`, not merely a lower axiom count.[^replay]

### What the conflict count does and does not mean

Z3 increments the exported `conflicts` statistic once whenever it resolves a
CDCL(T) conflict, regardless of whether the conflict originated in a Boolean
clause or a theory. A private SAT-origin subcount exists, but the standard
statistics do not export that split
([Z3 4.16 `resolve_conflict`](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/smt/smt_context.cpp#L4207-L4218),
[exported statistics](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/smt/smt_context_pp.cpp#L408-L430)).
Likewise, exported `propagations` sums watched-clause BCP; theory callbacks and
equality queues run separately and do not increment a generic theory-propagation
counter
([BCP counters](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/smt/smt_context.cpp#L310-L410),
[theory propagation loop](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/smt/smt_context.cpp#L1640-L1727)).

Native array reasoning can traverse parent-store/select pairs, filter duplicate
candidates, create equality antecedents, install relation watches, emit guarded
consequences, and revisit delayed work at final check without immediately
creating a conflict
([array candidate filtering](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/smt/theory_array_base.cpp#L221-L235),
[axiom-2 consequence construction](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/smt/theory_array_base.cpp#L139-L218),
[delayed propagation](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/smt/theory_array.cpp#L362-L412)).
Z3's own internals describe arrays as a reduction to EUF with throttled reduction
axioms ([Z3 Internals: Arrays](https://z3prover.github.io/papers/z3internals.html#sec-arrays)).

Thus the data is consistent with **many concrete array consequences remaining
dormant or cheap in CDCL conflict terms while specialized watches propagate
useful ones precisely**. It does not prove that CDCL "ignores useless lemmas".
The current counters have neither conflict provenance nor watch-activation and
consequence-use data, so that stronger claim is unmeasured.

### The workbook's instantiation plot is not an apples-to-apples comparison

For abstract, the report uses Yardbird's `total_instantiations_added`. For
concrete, it sums Z3's `array ax1` and `array ax2`
([`paper-graphics/src/benchmark_parsing.py:71-88`](../paper-graphics/src/benchmark_parsing.py#L71-L88)).
But Z3's `array ax2` counts accepted store/select pairs queued after filtering,
not emitted lemmas, active watches, or proof-used instances
([queue filtering](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/smt/theory_array_base.cpp#L221-L235),
[counter increment](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/smt/theory_array.cpp#L197-L220)).
The paired concrete totals are 2,793 `ax1`, 1,301,152 `ax2`, 5,170 expanded
`ax2`, and 75,774 extensionality events, but these cannot be compared directly
with 11,816 framed Yardbird instances.[^raw]

## Implication for demand-guided instantiation

The corrected design keeps one formula per refinement and uses a
property-rooted backward data-flow slice to prefer the next relevant array
formula
([demand-guided-instantiation.md](demand-guided-instantiation.md)). This keeps
the hypothesis interpretable and makes fewer instantiations, rather than eager
batching, the first objective:

- 135 of 175 successful abstract sessions refine; they have a median of two
  intermediate SAT checks. The SAT checks consume a median 5.6% of stock replay
  time within those sessions (IQR 3.1%-10.3%).[^captures]
- Across the successful abstract runs, `strategy_sat` work totals 29.224 s,
  versus 18.748 s in raw Z3 checks and only 75.6 ms in model acquisition.[^profiles]
  Removing refinement cycles can therefore materially improve Yardbird wall
  time even when it saves little Z3 conflict work.
- To improve **Z3** time, better selection must also reduce the later UNSAT
  formula's decisions, equality attempts, BCP, final checks, or resource count.
  Reordering formulas so that two cheap SAT checks become one much harder UNSAT
  check is a loss.

The evaluation should therefore treat later-UNSAT workload, unique indexed
equalities, and time outside `check_sat` as separate primary metrics.

## Prioritized next experiments

1. **Log demand rank in shadow mode.** Build the property-rooted demand graph,
   annotate the current candidate stream, and record which formula it would
   prefer without changing solver input. This validates coverage and exposes
   fallback frequency before timing a new heuristic.
2. **Measure the small equality reductions independently.** Start with exact
   `select(store(A, i, v), i) -> v` preprocessing, then count abstract,
   indexed, helper-definition, and unique asserted equalities before attempting
   canonical deduplication or demand-local frame placement.
3. **Run the rank-only demand experiment.** Compare the baseline selector with
   the demand-first selector while both emit exactly one formula per refinement.
   Require identical bounded outcomes, fewer timeouts, repeated in-process
   timing, and improvement in instantiations, Yardbird work, or later UNSAT
   workload—not check count alone.
4. **Use a stratified target set before a full sweep.** Start with
   `tiling_pnr2/3/4`; the large abstraction wins `tiling_skipped` and
   `two_counters_replace`; high SAT-share cases `array_init_monot_ind` (8 SAT
   checks, 63.4% of replay time), `array_two_counters_add` (7, 33.0%), and
   `array_scatter` (6, 28.7%); and all 14 abstract timeouts.[^captures][^raw]
5. **Test demand-local frame placement only after ranking.** Use selected-formula
   provenance to assert it at frames on the demanded path rather than every
   eligible frame, with full unrolling as the fallback.
6. **Finish the Z3 axiom-funnel instrumentation.** Per check, count array
   candidates, root-equal skips, fingerprint duplicates, queued pairs, processed
   dimensions, unit/binary consequences, relation watches installed and fired,
   and conflict provenance. The intended funnel is already specified in
   [`plans/z3-instrumentation.org:500-545`](../plans/z3-instrumentation.org#L500-L545).
   This directly tests the dormant-lemma hypothesis.
7. **Instrument the actual in-process C-API path.** Repeat Yardbird runs while
   timing assertion installation, check, model acquisition, and statistics
   collection inside the same stock Z3 build. The 11.47 s raw versus 62.77 s
   stock replay result for `pnr4` shows that shell replay is too path-sensitive
   to be the sole production metric.[^raw][^replay]
8. **Fix the reporting vocabulary.** Plot Yardbird asserted instances, Z3
   queued array pairs, emitted consequences, and activated consequences as
   separate series. Do not label their sum as a common "instantiation" unit.

Do not test top-k or eager consequence generation until rank-only selection has
improved formula order without increasing the number of formulas emitted.

## Measurement caveats

- The 14 abstract timeouts have no capture, so every paired replay result is
  conditioned on abstract success.[^run]
- Garden polls subprocess completion every 100 ms, making the workbook wall
  runtimes visibly quantized
  ([`garden/src/main.rs:295-345`](../garden/src/main.rs#L295-L345)).
- The workbook strategy summaries are medians over different populations; its
  abstract/concrete rows should not be read as paired effects
  ([`paper-graphics/report/instrumentation_data.py:30-48`](../paper-graphics/report/instrumentation_data.py#L30-L48)).
- Instrumented and stock external replay are not a pure overhead pair: the
  instrumented runner additionally fixes `sat.smt=false`, `smt.threads=1`,
  `proof=false`, and `combined_solver.ignore_solver1=true`
  ([`tools/z3_profile/instrumented.py:30-56`](../tools/z3_profile/instrumented.py#L30-L56)).
  Use stock external timing for performance and instrumented internal/envelope
  only for explanation.
- The abstract capture contains uninterpreted `Array_*`, `Read_*`, and `Write_*`
  symbols, not native arrays
  ([`src/theory_support.rs:232-295`](../src/theory_support.rs#L232-L295)).
  Its nonzero array envelope is array-plugin lifecycle/profiler baseline, not
  evidence that native array axioms were instantiated.
- Z3 incremental statistics are cumulative; meaningful check-level attribution
  requires before/after deltas, which the captures retain
  ([Z3 4.16 incremental search initialization](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/smt/smt_context.cpp#L3739-L3765),
  [`src/profiling.rs:237-259`](../src/profiling.rs#L237-L259)).
- This is one local, fixed-seed, depth-10 bounded run. `Success` means the bounded
  depths were ruled out; it is not an unbounded proof.[^raw]

## Evidence files

[^run]: Run manifest: [`run.json`](/Users/cvick-admin/.codex/worktrees/2568/yardbird/benchmark_results/main_eval/full-instrumented-z3/run.json), especially `instrumentation`, `subruns[0].comparison_counts`, and timing/config fields.
[^raw]: Raw 378-result evaluation: [`08_04_2026_23_02.json`](/Users/cvick-admin/.codex/worktrees/2568/yardbird/benchmark_results/main_eval/full-instrumented-z3/raw/light-review/08_04_2026_23_02.json). Derived paired statistics use `result.Success.solver_statistics.stats`, `total_instantiations_added`, and `run_time`, joined by cleaned example and strategy.
[^replay]: Session summary: [`instrumentation_comparisons.csv`](/Users/cvick-admin/.codex/worktrees/2568/yardbird/benchmark_results/main_eval/full-instrumented-z3/report/data/instrumentation_comparisons.csv), joined as 175 abstract/concrete pairs. Benchmark tails use the referenced `comparison_path` JSON and its 15-sample aggregate distributions.
[^captures]: Per-check classifications and statistics deltas: [`captures/light-review`](/Users/cvick-admin/.codex/worktrees/2568/yardbird/benchmark_results/main_eval/full-instrumented-z3/captures/light-review), specifically each `yardbird-profile.json` and paired comparison JSON.
[^profiles]: Sum over the 175 abstract `yardbird-profile.json` files' `driver_records[*].timing_secs.strategy_sat` and `solver_checks[*].timing_ns.model_acquisition`; raw-check total cross-checked against `solver_statistics.stats.solver_time` in the raw evaluation.
[^builder]: Z3 build identity and compiler settings: [`z3-builder-manifest.json`](/Users/cvick-admin/.codex/worktrees/2568/yardbird/benchmark_results/main_eval/full-instrumented-z3/instrumentation/z3-builder-manifest.json).
[^workbook]: Visually verified nine-page source workbook: [`workbook.pdf`](/Users/cvick-admin/.codex/worktrees/2568/yardbird/benchmark_results/main_eval/full-instrumented-z3/report/workbook.pdf), especially sections 2-4 and the conflict/instantiation/runtime plots.
[^config]: [`garden/benchmark_config.yaml:22-28`](../garden/benchmark_config.yaml#L22-L28) defines the `light-review` matrix and timeout.
[^report-aggregation]: The report takes independent medians per strategy group in [`paper-graphics/report/instrumentation_data.py:30-48`](../paper-graphics/report/instrumentation_data.py#L30-L48).
