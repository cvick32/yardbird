# Depth-50 abstract vs. concrete Z3 solver statistics

Date: 2026-08-06

Evaluation: `z3-deep-clean-aws-20260805_180440`

Status: research note; no report-generation changes

## Bottom line

The depth-50 run is substantially stronger evidence for array abstraction than
the earlier depth-10 run, but it also sharpens what the conflict counter means:

1. **Abstraction wins at depth 50.** It completed 156/189 benchmarks versus
   149/189 for concrete Z3, including 19 abstract-only and 12 concrete-only
   completions. On the 137 shared completions, the geometric-mean wall-time
   speedup is 1.202x and the geometric-mean raw Z3-check speedup is 1.334x.[^run][^workbook][^raw]
2. **The end-to-end win comes from large Z3 savings, not fewer refinement
   checks.** Abstract performs 7,224 checks over the shared set versus 6,850
   concrete checks, but uses 995.9 versus 2,686.0 seconds inside `check_sat`.
   The paired check-count ratio has essentially no association with the paired
   Z3-time ratio (Spearman rho = -0.012).[^raw]
3. **"Abstract has more conflicts" is true only as a central-distribution
   summary.** Abstract has more conflicts in 67 shared pairs, fewer in 50, and
   the same number in 20. Its median conflict count is 5,012 versus 2,879, but
   the median paired ratio is exactly 1.00. Its aggregate is actually lower:
   1.474M versus 1.670M conflicts.[^raw]
4. **Most speed wins are not conflict paradoxes.** Among the workbook's 52
   wall-time wins, abstract has fewer conflicts in 40 and more in only 12; the
   median conflict ratio is 0.793. Among the 74 direct-Z3 wins, abstract has
   more conflicts in 21. Those 21 are the cases that should be used to study
   why conflicts can have very different cost.[^raw]
5. **The best current predictor of paired Z3 speed is the resource count,
   followed by decisions, conflicts, added equalities, and propagations.** The
   paired-ratio Spearman correlations with the Z3-time ratio are 0.891, 0.814,
   0.764, 0.756, and 0.713 respectively. These counters are highly collinear,
   so this ranks useful plotting signals; it does not identify an independent
   causal operation.[^raw]
6. **Binary propagation, final checks, and interface equalities are encoding
   fingerprints, not useful standalone cost predictors in this run.** Abstract
   performs far more of all three, even in many large wins, while their
   paired-ratio correlations with Z3 time are only 0.270, 0.023, and -0.305.[^raw]

The immediate reporting change should therefore be a set of paired
**solver-time-speedup versus counter-reduction** plots, not more cactus plots of
absolute counts. The array-envelope run will later explain which native array
callbacks produced the concrete workload; this clean run already shows how the
resulting generic CDCL(T) workload scales.

## Experiment and measurement boundary

Both AWS subruns used Yardbird commit
`fe01d2e6b6e2232b588d919198863b11e52f48e1`, depth 50, BMC cost, a 120-second
per-benchmark timeout, and no solver-journal capture. All 305 successful entries
completed the bounded depth without a counterexample or unbounded proof. The
population is:[^run][^config][^raw]

| Outcome | Count |
|---|---:|
| Abstract successful | 156 |
| Concrete successful | 149 |
| Both successful | 137 |
| Abstract only | 19 |
| Concrete only | 12 |
| Both timed out | 21 |

All paired statistics below use only the 137 shared successful benchmarks.
That avoids mixing populations, but it excludes precisely the 31 differential
timeouts. Coverage must therefore be reported beside paired performance.

Two time boundaries are kept separate:

- **Wall time** is Garden's subprocess runtime. Garden's completion polling
  makes short observations visibly quantized at roughly 100 ms
  ([`garden/src/main.rs:295-345`](../garden/src/main.rs#L295-L345)).
- **`solver_time`** is Yardbird's sum of elapsed calls to Z3 `check_sat`. It is
  accumulated after each check
  ([`src/solver/z3.rs:145-171`](../src/solver/z3.rs#L145-L171)); property
  push/pop, model acquisition, statistics collection, e-graph work, and
  refinement scheduling are outside this timer
  ([`src/solver/check.rs:30-78`](../src/solver/check.rs#L30-L78)).

The raw Z3 statistics are cumulative over the incremental solver lifetime.
Z3 omits zero-valued keys, so absent counters are treated as zero. Ratios quoted
for sparse counters use only pairs where both sides are positive. The paired
correlation uses `log1p(abstract_counter) - log1p(concrete_counter)` against
`log(abstract_solver_time / concrete_solver_time)` and reports Spearman rank
correlation.[^raw][^z3-stats]

## End-to-end result versus direct Z3 result

| Paired metric | Abstract | Concrete | Median paired A/C | Aggregate A/C |
|---|---:|---:|---:|---:|
| Wall time | 0.502 s | 0.401 s | 1.000 | 1,150.8 / 2,707.2 s |
| Raw Z3-check time | 0.325 s | 0.282 s | 0.943 | 995.9 / 2,686.0 s |
| Checks | 52 | 50 | 1.040 | 7,224 / 6,850 |
| Conflicts | 5,012 | 2,879 | 1.000 | 1.474M / 1.670M |
| Decisions | 23,306 | 9,249 | 1.106 | 12.44M / 19.25M |
| Propagations | 148,443 | 76,310 | 1.392 | 137.2M / 180.0M |
| Binary propagations | 64,687 | 100 | 1.672 | 66.38M / 26.71M |
| Added equality attempts | 83,325 | 37,323 | 1.000 | 193.97M / 421.70M |
| Resource count | 991,259 | 441,264 | 1.146 | 1.875B / 4.223B |
| Clauses created | 26,896 | 104,694 | 0.247 | 8.86M / 42.30M |
| Boolean variables created | 19,945 | 64,688 | 0.328 | 8.70M / 67.65M |
| Binary clauses created | 480 | 140 | 1.819 | 127,184 / 44,252 |
| Final checks | 1,097 | 0 | sparse | 253,888 / 25,829 |
| Interface equalities | 23 | 0 | sparse | 133,375 / 18,730 |

The apparent tension between the median and aggregate columns is the main
scale effect. On many small or moderate benchmarks, abstract performs the same
or more generic work. On the expensive benchmarks where concrete Z3 grows
badly, abstraction removes enough decisions, equalities, clauses, and resource
work to dominate the aggregate and geometric mean. No single benchmark
controls the result: the largest paired concrete Z3 time is 4.4% of its total,
and the largest abstract time is 8.8% of its total.[^raw]

The 52 wall-time wins alone account for 798.9 seconds of abstract Z3 time versus
2,597.3 seconds of concrete Z3 time. Within those wins, abstract uses 24% fewer
conflicts, 43% fewer decisions, 62% fewer added equalities, 63% less resource
count, 82% fewer non-binary clauses, and 89% fewer Boolean variables in
aggregate. It nevertheless performs 2.14x as many binary propagations, 2.42x as
many binary-clause creations, 7.12x as many final checks, and 10.48x as many
interface equalities.[^raw]

This says the abstract encoding still shifts work toward guarded binary
consequences and EUF interface activity, just as the shallow run suggested. At
depth 50, however, the smaller general clause/variable/equality search state
more than pays for that shift on the expensive instances.

## Resolving the conflict-count puzzle

Z3's exported `conflicts` counter increments when the CDCL(T) context resolves
a conflict. It does not count theory lemmas, does not retain their provenance,
and does not weight conflicts by the size of the trail, clause database,
equality state, or theory work needed to reach them
([Z3 `resolve_conflict`](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/smt/smt_context.cpp#L4207-L4218),
[statistics export](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/smt/smt_context_pp.cpp#L408-L430)).
`propagations` is the sum of watched-clause BCP counters, while theory
propagation and equality processing have separate paths
([BCP](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/smt/smt_context.cpp#L310-L410),
[theory propagation](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/smt/smt_context.cpp#L1640-L1727)).

Consequently, the same number of conflicts can correspond to very different
work. Across shared pairs, the descriptive median `solver_time / count` is:

| Normalization | Abstract | Concrete |
|---|---:|---:|
| Time per conflict | 103.2 us | 131.4 us |
| Time per decision | 32.8 us | 81.2 us |
| Time per propagation | 4.61 us | 5.44 us |
| Time per added equality | 5.12 us | 7.67 us |
| Time per resource unit | 288 ns | 566 ns |

These are not causal unit prices: each numerator contains all solver work, and
the denominator events are correlated. They do demonstrate why raw event
counts cannot be treated as equal-cost units.

The cleanest "more conflicts but faster" subset contains 21/74 direct-Z3 wins.
Within it, abstract has median ratios of 1.445 conflicts, 1.576 decisions, 1.562
propagations, 1.384 added equalities, and 1.354 resource count, yet is 1.506x
faster in median. Its time-per-conflict ratio is 0.483. The structural contrast
is that it creates only 0.176x as many non-binary clauses and 0.129x as many
Boolean variables in median.[^raw]

The strongest examples make the missing weighting visible:

| Benchmark | Z3 speedup | Conflict A/C | Decision A/C | Propagation A/C | Added-eq A/C | Resource A/C | Time/conflict A/C |
|---|---:|---:|---:|---:|---:|---:|---:|
| `array_tiling_tcpy2` | 6.73x | 1.11 | 0.20 | 1.75 | 0.82 | 0.37 | 65.8 / 491.5 us |
| `array_tiling_tcpy3` | 5.85x | 1.13 | 0.25 | 1.66 | 0.78 | 0.39 | 52.4 / 346.4 us |
| `array_init_addvar7` | 2.70x | 1.45 | 1.62 | 0.95 | 0.45 | 0.47 | 257.5 / 1,004.4 us |
| `array_init_ite` | 2.10x | 1.58 | 2.32 | 3.08 | 0.30 | 1.47 | 85.6 / 284.6 us |

For `tcpy2/3`, more cheap abstract conflicts coexist with far fewer decisions
and resource work. `init_addvar7` points more specifically at equality and
formula-state reduction. `init_ite` is a warning that even the resource counter
is not a uniform CPU unit: Z3's resource limit is a counter advanced by calls
to `inc()` or weighted `inc(offset)`, not an instruction or elapsed-time
counter
([`rlimit.h`](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/util/rlimit.h#L27-L68),
[`rlimit.cpp`](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/util/rlimit.cpp#L34-L48)).

The right conclusion is not "conflicts do not matter." Conflict reduction is
strongly associated with speedup, but **conflict count is an unweighted search
volume signal**. We need the other counters and per-check state to explain the
cost of reaching and resolving those conflicts.

## Which counters track solve time?

| Counter | rho within abstract | rho within concrete | rho paired Z3 ratio | rho paired wall ratio |
|---|---:|---:|---:|---:|
| Resource count | 0.982 | 0.991 | **0.891** | **0.810** |
| Decisions | 0.920 | 0.957 | **0.814** | 0.687 |
| Conflicts | 0.922 | 0.975 | **0.764** | 0.672 |
| Added equalities | 0.960 | 0.978 | **0.756** | 0.672 |
| Propagations | 0.945 | 0.965 | **0.713** | 0.681 |
| Boolean variables | 0.926 | 0.947 | 0.660 | 0.545 |
| Arithmetic conflicts | 0.898 | 0.840 | 0.622 | 0.544 |
| Clauses created | 0.933 | 0.902 | 0.550 | 0.414 |
| Binary propagations | 0.921 | 0.731 | 0.270 | 0.300 |
| Final checks | 0.413 | 0.210 | 0.023 | 0.035 |
| Interface equalities | 0.779 | 0.235 | -0.305 | -0.248 |

The within-strategy columns mostly measure benchmark size: every cumulative
counter grows on harder instances. The paired columns are more useful because
they ask whether changing the counter between encodings tracks changing time
on the same benchmark. Resource count is the best single summary, but it is
also highly correlated with the decision, conflict, propagation, and
added-equality ratios (rho 0.83-0.90). A multivariate causal interpretation is
not available from 137 one-shot observations.[^raw]

For concrete Z3 alone, native `array ax2` has rho 0.837 with solver time and
`array ext ax` has rho 0.689, compared with 0.975 for conflicts and 0.991 for
resource count. Those array counters are useful scaling indicators but still do
not say whether the generated consequences were activated or useful. The
instrumented envelope/funnel run is needed for that attribution.[^raw][^shallow]

## Important wall-time exceptions

The largest workbook regressions should not all be interpreted as Z3
regressions. Two `array_split` cases are the opposite:

| Benchmark | Wall A/C | Raw Z3 A/C | Checks A/C |
|---|---:|---:|---:|
| `array_split_21` | 68.51 / 5.30 s | 0.199 / 5.174 s | 72 / 50 |
| `array_split_20` | 50.40 / 5.10 s | 0.231 / 4.921 s | 73 / 50 |

Z3 is 26x and 21x faster under abstraction, but Yardbird spends roughly 68 and
50 seconds outside `check_sat`, most likely in repeated model/e-graph/refinement
work. These are prime demand-ranking, frame-placement, and strategy-overhead
targets. In contrast,
`array_nonlin_square` is a real solver regression: abstract/concrete Z3 time is
14.97/0.70 seconds and wall time is 15.21/0.80 seconds.[^raw]

This separation matters for the research goal. Demand-guided instantiation can
win end-to-end by removing expensive refinement processing even when it does
not reduce Z3 counters, while improving Z3 itself requires reductions in the
later search workload.

## Comparison with the shallow evaluation

The depth-10 evaluation found abstraction slower end-to-end, a 1.165 median
conflict ratio, and higher generic-work ratios, even though its one-shot raw
Z3-check geometric mean already modestly favored abstraction (A/C 0.797). At
depth 50:[^shallow]

- the raw Z3 geometric mean improves to A/C 0.750;
- the end-to-end geometric mean crosses over to A/C 0.832;
- coverage changes from 14 abstract-only timeouts to a net seven-completion
  advantage;
- the abstract encoding still has much more binary BCP, binary clause creation,
  final checking, and interface equality activity;
- expensive concrete cases now provide broad, not one-case, savings.

The key scale transition is therefore amortization plus avoidance of large
concrete search states. It is not a suite-wide collapse in abstract conflict
counts. The earlier `array_tiling_pnr2/3/4` diagnostic family cannot be compared
at depth 50 because all six strategy/family combinations timed out and emitted
no final statistics in this clean run.[^results]

## Solver-stat plots now in the workbook and next additions

The regenerated workbook now includes the first two views below and paired
counter panels for conflicts, decisions, propagations, added equalities,
resource count, clauses, and Boolean variables. The remaining views are the
next useful additions:

1. **Implemented: paired counter reduction versus Z3 speedup.** One panel per
   counter, with `x = log10((concrete_counter + 1) / (abstract_counter + 1))`
   and `y = log10(concrete_solver_time / abstract_solver_time)`. Draw zero
   quadrant lines; color wall win/tie/loss; annotate `tcpy2/3`, `init_addvar7`,
   `init_ite`, `nonlin_square`, and the largest tail wins.
2. **Implemented: wall speedup versus raw Z3 speedup.** This separates solver improvements
   from Yardbird overhead and will make `split_20/21` immediately visible.
3. **Conflict price plot.** Plot `solver_time / conflicts` against conflicts,
   with Boolean-variable or clause count as color/marker size. This is a
   descriptive visualization, not a causal per-conflict cost model.
4. **Within-strategy scaling panels.** Log-log solver time against resource
   count, decisions, conflicts, added equalities, and clauses. Show abstract
   and concrete separately and include rho in each panel.
5. **Per-depth delta traces for selected cases.** Use the existing
   `unsat_events[*].solver_stats_delta` to plot time, conflicts, decisions,
   equality attempts, and resource work by BMC depth. Start with `tcpy2/3`,
   `init_addvar7`, `init_ite`, `nonlin_square`, and a large conventional win.
   The delta from one UNSAT depth to the next includes any intervening abstract
   refinement checks, which should be labeled explicitly.
6. **Censored coverage panel.** Keep the 19/12 exclusive completions and 21
   joint timeouts visible. Do not silently drop them from paired scatter plots.

Do not combine Yardbird's explicit-instantiation count with Z3 `array ax1/ax2`
as a common unit; the shallow note documents why those counters have different
semantics ([`paper-graphics/src/benchmark_parsing.py:71-88`](../paper-graphics/src/benchmark_parsing.py#L71-L88)).

## Measurement caveats

- This is one fixed-seed run per strategy on separate AWS instances, not a
  repeated timing experiment. Long effects are large, but near-ties should be
  revisited with repeated local replay or repeated in-process runs.[^run]
- The 120-second timeout censors 52 strategy-results, including all depth-50
  `pnr2/3/4` cases. Final Z3 statistics are unavailable for timed-out clean
  processes.[^results]
- Wall-time polling is coarse for the many 0.1-0.5 second entries. Prefer raw
  `solver_time` for solver-stat association and use wall time for the delivered
  end-to-end result.
- Cumulative counters are not independent operations. Reducing a decision can
  also reduce propagation, conflict, equality, clause, and resource counts.
- A conflict has no exported provenance or weight. The upcoming instrumented
  array run is still required to distinguish array candidates, emitted
  consequences, watch activations, theory propagation, and downstream
  conflicts.
- `Success` here means all requested bounded depths were discharged; it is not
  an unbounded proof.[^raw]

## Reproduction

Regenerate the canonical report and inspect the workbook text:

```bash
python3 main_eval.py \
  --run-id z3-deep-clean-aws-20260805_180440 \
  --generate-report

pdftotext -layout \
  benchmark_results/main_eval/z3-deep-clean-aws-20260805_180440/report/workbook.pdf \
  -
```

Verify the paired population, geometric means, event totals, and paired-ratio
correlations using only the standard library:

```bash
python3 - <<'PY'
import json, math, pathlib, statistics as st

root = pathlib.Path(
    "benchmark_results/main_eval/z3-deep-clean-aws-20260805_180440/raw"
)

def load(strategy):
    path = next((root / strategy).glob("*.json"))
    data = json.loads(path.read_text())
    rows = {}
    for benchmark in data["benchmarks"]:
        name = benchmark["example"].split("_examples/", 1)[1]
        entry = benchmark["result"][0]
        result = entry["result"]
        if "Success" not in result:
            rows[name] = None
            continue
        success = result["Success"]
        rows[name] = {
            "wall": entry["run_time"] / 1000.0,
            "stats": {
                key: float(value)
                for key, value in success["solver_statistics"]["stats"].items()
            },
        }
    return rows

def ranks(values):
    order = sorted(range(len(values)), key=values.__getitem__)
    result = [0.0] * len(values)
    i = 0
    while i < len(order):
        j = i + 1
        while j < len(order) and values[order[j]] == values[order[i]]:
            j += 1
        rank = (i + j - 1) / 2.0 + 1.0
        for index in order[i:j]:
            result[index] = rank
        i = j
    return result

def pearson(xs, ys):
    xbar, ybar = st.mean(xs), st.mean(ys)
    dx, dy = [x - xbar for x in xs], [y - ybar for y in ys]
    return sum(x*y for x, y in zip(dx, dy)) / math.sqrt(
        sum(x*x for x in dx) * sum(y*y for y in dy)
    )

def spearman(xs, ys):
    return pearson(ranks(xs), ranks(ys))

abstract, concrete = load("deep-abstract"), load("deep-concrete")
paired = sorted(k for k in abstract if abstract[k] and concrete[k])
print("successful/paired:",
      sum(v is not None for v in abstract.values()),
      sum(v is not None for v in concrete.values()), len(paired))

def stat(rows, benchmark, key):
    return rows[benchmark]["stats"].get(key, 0.0)

def gmean(values):
    return math.exp(st.mean(math.log(value) for value in values))

print("geometric A/C wall, solver:",
      gmean([abstract[k]["wall"] / concrete[k]["wall"] for k in paired]),
      gmean([stat(abstract, k, "solver_time") /
             stat(concrete, k, "solver_time") for k in paired]))

for key in ["solver_time", "num checks", "conflicts", "decisions",
            "propagations", "binary propagations", "added eqs",
            "rlimit count", "mk clause", "mk bool var", "final checks",
            "interface eqs"]:
    av = [stat(abstract, k, key) for k in paired]
    cv = [stat(concrete, k, key) for k in paired]
    print(key, "median", st.median(av), st.median(cv),
          "sum", sum(av), sum(cv))

solver_ratios = [
    math.log(stat(abstract, k, "solver_time") /
             stat(concrete, k, "solver_time"))
    for k in paired
]
for key in ["rlimit count", "decisions", "conflicts", "added eqs",
            "propagations", "mk bool var", "arith-conflicts", "mk clause",
            "binary propagations", "final checks", "interface eqs",
            "num checks"]:
    counter_ratios = [
        math.log1p(stat(abstract, k, key)) -
        math.log1p(stat(concrete, k, key))
        for k in paired
    ]
    print(key, "paired-ratio rho", spearman(counter_ratios, solver_ratios))
PY
```

## Evidence files

[^run]: Completed run manifest: [`benchmark_results/main_eval/z3-deep-clean-aws-20260805_180440/run.json`](../benchmark_results/main_eval/z3-deep-clean-aws-20260805_180440/run.json). It records the two completed AWS subruns, common commit, disabled journal capture, and report paths.
[^workbook]: Visually verified 17-page regenerated workbook: [`report/workbook.pdf`](../benchmark_results/main_eval/z3-deep-clean-aws-20260805_180440/report/workbook.pdf), especially the paired Z3 diagnostics table, counter-reduction panels, and Z3-versus-end-to-end panel.
[^raw]: Primary benchmark data: [`raw/deep-abstract/08_05_2026_18_04.json`](../benchmark_results/main_eval/z3-deep-clean-aws-20260805_180440/raw/deep-abstract/08_05_2026_18_04.json) and [`raw/deep-concrete/08_05_2026_18_04.json`](../benchmark_results/main_eval/z3-deep-clean-aws-20260805_180440/raw/deep-concrete/08_05_2026_18_04.json). Derived statistics join cleaned benchmark paths and use `run_time`, `result.Success.solver_statistics.stats`, and success flags.
[^results]: Normalized result and paired classification tables: [`benchmark_results.csv`](../benchmark_results/main_eval/z3-deep-clean-aws-20260805_180440/report/data/benchmark_results.csv) and [`benchmark_comparisons.csv`](../benchmark_results/main_eval/z3-deep-clean-aws-20260805_180440/report/data/benchmark_comparisons.csv).
[^config]: [`garden/benchmark_config.yaml:59-100`](../garden/benchmark_config.yaml#L59-L100) defines both depth-50 matrices and the 120-second timeout.
[^z3-stats]: Z3 exports the cumulative SMT-context counters together in [`context::collect_statistics`](https://github.com/Z3Prover/z3/blob/z3-4.16.0/src/smt/smt_context_pp.cpp#L408-L430). Yardbird overwrites the latest Z3 snapshot while accumulating its custom elapsed solver time in [`src/solver/z3.rs:58-65`](../src/solver/z3.rs#L58-L65) and [`src/solver/z3.rs:168-171`](../src/solver/z3.rs#L168-L171).
[^shallow]: Earlier depth-10 analysis and Z3-stat semantics: [`plans/z3-abstract-vs-concrete-eval.md`](z3-abstract-vs-concrete-eval.md), especially "Paired central tendency," "What the conflict count does and does not mean," and "Measurement caveats."
