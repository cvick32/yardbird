# Implementation validation

Validated locally on 2026-09-12/13 using the rebuilt release Yardbird binary and
Codex CLI with `gpt-6-astra`, reasoning effort `high`.

## Automated checks

- 20 pytest tests pass, including complete 10- and 15-run mock investigations,
  configuration/parent/budget validation, scheduler serialization, resume,
  native Yardbird statistics, queries, process cancellation and external kills.
- Ruff lint and formatting checks pass. Git whitespace checks pass.
- A native array-copy result is retained in `tests/fixtures/array-copy-result.json`.

## Live agent integration

Campaign: `.scratch/benchmark-investigator/live-copy/`.

One actual Astra investigation completed all 15 executions, issued RUN,
ANALYZE_PROFILE, INSPECT_SOURCE and FINISH actions, and wrote:

`FINDINGS/FINDINGS-array_copy-e4aac70c.md`.

This integration test used depth 3 and a 10-second execution timeout. It validates
the workflow rather than the deeper benchmark performance claims. All 15 runs
completed depths 0–2. The report identified an e-graph construction bottleneck,
distinguished startup/timing noise from parameter effects, and recommended finer
instrumentation rather than claiming an unproven optimization.

The first backend launch was blocked by the desktop execution sandbox; the live
CLI needed its usual local state/account access. Once allowed, structured output
and disabled experiment tools worked. During the pilot, repeated source lookups
motivated retaining recent investigation evidence and the full list of prior
inspection requests. The live campaign was interrupted and resumed to load that
improvement, preserving completed runs. A pilot-only history document was also
added to its context; every invocation's exact prompt is archived.

## Three-benchmark baseline pilot

Campaign: `.scratch/benchmark-investigator/pilot-baselines/`.

All runs used depth 20 and the planned 300-second cooperative timeout with a
10-second external safety margin. Abstract configurations use the canonical
baseline; concrete references retain assumptions property checks.

| Benchmark | Strategy | Outcome | Wall seconds | Deepest completed depth | Profile |
|---|---|---|---:|---:|---|
| array_copy | abstract | depth_limit | 0.540 | 19 | retained |
| array_copy | concrete | depth_limit | 0.016 | 19 | retained |
| German | abstract | depth_limit | 35.854 | 19 | retained |
| German | concrete | external_timeout | 310.010 | unknown | unavailable |
| Chord ring maintenance | abstract | timeout | 301.023 | 1 | retained |
| Chord ring maintenance | concrete | solver_unknown | 0.024 | 1 | retained |

These are single observations on a shared host, not statistical comparisons. They
verify outcome handling, useful timeout profiles, nonzero-exit JSON capture, and
the explicit missing-data path for a hard kill. The German external timeout does
not permit inferring progress. Chord's concrete unknown is not ranked as a fast
successful run.

Completed summaries were regenerated after correcting native `stats` nesting;
raw profiles and process logs were left intact. Source and binary pins were
verified after validation.

## Remaining operational scope

The full 40-benchmark campaign has not been launched. The pilot configuration and
CLI default to 10-run investigations, with explicit 15-run configuration supported.
The 31-benchmark distributed-protocol encoding configuration is prepared but has
not been launched.
Per-binder attribution remains explicitly unavailable until Yardbird exports the
needed mapping/counts. CPU affinity, memory enforcement, distributed execution,
automatic code changes and heavy crash recovery remain intentionally deferred.
The synthesis endpoint is implemented; no cross-benchmark research synthesis was
requested from the baseline-only pilot, which has no per-benchmark findings yet.
