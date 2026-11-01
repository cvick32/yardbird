# Post-hoc core utilization

For each strategy, replay only benchmarks whose original result was `Success`. Reconstruct the abstract BMC query at the requested final frame, assert all saved `used_instances` schemas at their eligible frames, extract a fresh Z3 UNSAT core, and measure:

- **Schema utilization:** distinct saved schemas with at least one assertion in the replay core / distinct saved schemas.
- **Assertion utilization:** replayed frame-indexed assertions in that core / replayed assertions.

This needs no historical cores, new model calls, or refinement search. The original VMT source is loaded from the run's recorded Git revision. Default final frame is `depth - 1` (49 for depth 50); `--depth` overrides this with a zero-based frame. Relative offsets and full-unroll placement follow `BMCBuilder` and `instance_installation`: a width-W schema is placed at ending frames W through the final frame. A symbol `x+K` at ending frame F becomes `x@(F-W+K)`; unframed state variables become their F versions.

Run from the repository root, using the paper-graphics environment (which includes `z3-solver`):

```bash
paper-graphics/.venv/bin/python paper-graphics/core_utilization.py \
  benchmark_results/main_eval/ut-instantiation-depth50-aws-20261028_151413 \
  --output benchmark_results/main_eval/ut-instantiation-depth50-aws-20261028_151413/report/core-replay \
  --timeout-seconds 10
```

For one example, append `--examples array_two_counters_replace.vmt --save-queries`. `--methods openai jev yardbird` is the default. Input can also be one or more Garden result JSON files. `--save-queries` writes replayable SMT-LIB queries and label-to-schema/frame mappings. Reports are written incrementally as JSON, CSV, and Markdown; each row includes status, source hash, source revision, target frame, counts, and core membership.

The script supports the quantifier-free Int-array VMT inputs and abstract/full-unroll configuration used by this evaluation. It supports constant arrays, source helper definitions, and multi-frame saved schemas. It rejects unsupported encodings or transformations rather than silently changing the query. Original `Timeout`, `NoProgress`, and other unsuccessful outcomes are excluded before source loading or replay, even if they saved schemas. Their counts appear separately in `excluded_original_outcomes` and the report; they never enter the replay denominator. An originally successful result without saved schemas is marked `missing_schemas`. Accepted proposal logs alone are not assumed to be a complete installed list. Replay SAT, timeout/unknown, missing schemas, and zero denominators have no utilization percentage.

These are **post-hoc replay cores**, not cores from the original incremental run. Only the property at the selected final frame is checked; an UNSAT replay does not establish all earlier bounds or upgrade the outcome of an originally failed run. A solver-produced core need not be minimal. Absence from this final-bound core does not establish that an instance was useless at earlier bounds. Pooled summaries use only UNSAT replays and keep configurations and depths separate; compare common benchmark cohorts at the same bound for method comparisons. Each method has its own replay/core, so this is utilization within a method, not a share of one joint core across methods. Native Z3's internal array reasoning has no comparable saved external-schema list.

A successful original run can still time out during fresh replay: the final formula is solved without the original incremental solver state, and assertion order/presentation can strongly affect runtime. The default ten-second replay budget is independent of the original 120-second run budget. Unknown/timeout results remain explicit missing measurements; the report's UNSAT/replay counts show coverage. A checked `array_init_disj` replay has the same 496 normalized conjuncts as Yardbird's dump but still times out even at 120 seconds, including a ten-second timeout without core tracking. See the run report's `core-replay/timeout-diagnosis/` for the captured experiments.
