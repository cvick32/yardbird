# Yardbird benchmark investigator

A Python CLI for bounded benchmark investigations: one pinned Yardbird binary,
10 executions per benchmark by default, deterministic profile summaries, SQLite lineage,
and short-lived Codex decisions. This is separate from Garden and does not change
Yardbird's verification algorithms.

## Setup

From the repository root:

```sh
uv sync --project tools/benchmark_investigator
uv run --project tools/benchmark_investigator investigator --help
```

macOS or Linux, Python 3.11+, Cargo/Z3 for a new release build, and an authenticated Codex CLI for
agent investigations are required. The dependency lock is included. Tests and the
mock backend do not require Codex or network access.

## One experiment

```sh
cargo build --release -p yardbird
uv run --project tools/benchmark_investigator investigator run \
  examples/array/array_copy.vmt tools/benchmark_investigator/baseline.json \
  --output .scratch/investigator-single
```

This runs a prebuilt binary directly with `--profile --json-output` and a cooperative
300s deadline plus a 10s external kill margin. It writes `action.json`, `config.json`,
`metadata.json`, stdout/stderr logs, `result.json`, `profile.json`, `summary.json`,
and `summary.md`. The output directory must not exist. Use `--binary`, `--depth`,
`--timeout`, and `--kill-grace` for validation runs. Only array VMT inputs are supported.

Read `termination_reason`, not just the process status: Yardbird emits partial
profiles for controlled failures. External kills, malformed output and spawn errors
are separate outcomes. A missing profile is JSON null, not an empty successful run.
The shell command exits successfully when artifacts were collected; inspect metadata
for the solver outcome. Python/subprocess wall time includes startup and cleanup;
Yardbird's driver elapsed time excludes parsing.

## Create and run a campaign

```sh
uv run --project tools/benchmark_investigator investigator init \
  tools/benchmark_investigator/pilot.json --output .scratch/investigator-pilot
uv run --project tools/benchmark_investigator investigator campaign \
  .scratch/investigator-pilot --baselines-only
uv run --project tools/benchmark_investigator investigator status .scratch/investigator-pilot
uv run --project tools/benchmark_investigator investigator campaign \
  .scratch/investigator-pilot --backend codex
```

`distributed-protocols-encodings.json` lists all 31 `*.encoding.vmt` files under
`examples/distributed_protocols/`, including the German ghost-state variant. It
uses 10 executions per benchmark (310 total) and serial run/agent scheduling.
Pass this file to `init` when ready to start the encoding campaign; preparing the
configuration does not initialize or launch a campaign.

`init` builds release Yardbird once (or accepts `--binary`), copies a single pinned
executable to the campaign context, hashes source and benchmarks, records Git SHA,
host/build metadata and Z3 CLI version, and copies three agent reference documents.
Actual Z3 runtime versions are captured per run from Yardbird's stderr. A provided
binary is recorded as such: its relationship to source is the caller's responsibility.
Source, benchmark, ranker and binary drift are rejected before experiments. There
are no worktrees. Do not edit the pinned source checkout during a campaign.

The pilot config contains array_copy, German and Chord candidates. Their easy/slow/
concrete-gap roles must be confirmed against the actual baseline results, not assumed
from historical measurements. Defaults are depth 20 (zero-based depths 0–19), 300s,
10 executions and Astra High (`gpt-6-astra`, `high`). These are campaign
configuration; `executions_per_benchmark` can explicitly select 15 for a deeper
investigation. Existing 15-run campaigns retain their configured budget. Serial
execution in the pilot reduces timing interference.
Increase scheduler.max_parallel_runs and max_parallel_agents for a larger cohort.
CPU/memory reservations are descriptive metadata in v1; affinity/cgroups are not
implemented. Start another campaign for different source or policy settings.

Runs 1/2 are enforced abstract baseline/concrete reference. Runs 3–10 (or through the configured budget) require an
abstract parent from the same benchmark. At most three of five dimensions may
change. Unknown knobs, unsupported values, concrete parents, cross-benchmark
parents, and logistic regression without a pinned model are rejected before a run.
FINISH is accepted after the configured number of executions. Each benchmark has at most 100
agent decisions, including rejected requests. A model failure marks only that
benchmark as needing attention; other investigations can finish.

Each model invocation proposes one action and exits before Yardbird runs. The
backend uses the installed Codex CLI with structured output, read-only sandbox,
no approval prompts, ignored user config/rules, and disabled shell, plugins, apps,
subagent and browser tools. Source inspection and experiments are dispatched by
the harness. Model/reasoning selection and decision timeout remain configurable.
No API key is read by the harness; authentication remains with Codex.

CLI discovery uses `CODEX_EXECUTABLE` when set; otherwise it searches PATH for
`codex`, then the macOS ChatGPT app under `/Applications` or `~/Applications`.
An invalid explicit override fails rather than selecting another executable.
Missing executables are rejected before any campaign runs begin. Baseline-only
and mock campaigns do not require Codex. For a custom installation:

```sh
export CODEX_EXECUTABLE="/absolute/path/to/codex"
```

If discovery failed after an older runner saved the baseline runs, rerun the
`campaign` command with the same directory. Completed executions are reused;
do not run `init` again.

The CLI flags were verified against the local CLI and the official
[non-interactive documentation](https://developers.openai.com/codex/noninteractive/).

## Manual experiments, queries and reports

After `--baselines-only`, create an action file using the baseline run ID from SQLite
or `benchmarks/<id>/runs/`:

```json
{
  "action": "RUN",
  "parent_run_id": "<abstract-run-id>",
  "config_patch": {"cost_function": "index-aware", "candidate_winners_per_group": 5},
  "hypothesis": "Smaller batches reduce expensive candidate processing",
  "expected_signal": "Lower grounding time without losing completed depth",
  "rationale": "The baseline spends most time in grounding"
}
```

```sh
uv run --project tools/benchmark_investigator investigator experiment \
  .scratch/investigator-pilot <benchmark-id> action.json
uv run --project tools/benchmark_investigator investigator summarize <run-directory>
uv run --project tools/benchmark_investigator investigator query <run-directory> refinement --depth 2 --refinement-step 0
uv run --project tools/benchmark_investigator investigator synthesize .scratch/investigator-pilot
```

Summaries are derived artifacts and can be regenerated. Run inputs/logs/raw results
are never overwritten by the harness. Queries return bounded valid JSON and explicitly
mark truncation. Timing percentages use wall time because timers overlap. Per-rule
counts are available; explicit per-binder attribution remains unavailable in Yardbird
and is marked as missing. The profiling guide documents these limits.

The campaign writes compact `FINDINGS-<id>.md` files beside each benchmark and under
`FINDINGS/`; synthesis consumes completed reports and writes `SYNTHESIS.md`. Evidence
run IDs are validated. A fivefold runtime difference or concrete success versus an
incomplete abstract baseline raises `LARGE_CONCRETE_ABSTRACT_GAP`. Treat rankings as
observations, not statistical confidence: this version has no dedicated confirmation
run machinery. Repeated identical configurations are legal evidence-gathering runs.

Completed experiments are reused when a campaign resumes. A filesystem lock prevents
two CLI processes from operating the same campaign, and an async lock prevents two
runs for one benchmark. Interrupted/unfinalized attempts require inspection and are
not automatically repeated or refunded. Raw stdout/stderr remain on disk. There is
no crash recovery, distributed scheduler, automatic code editing or web UI.

For smoke tests, `campaign --backend mock` uses a deterministic cost-function cycle.
Its reports prominently say MOCK BACKEND and cannot be used for research synthesis.

## Validation

```sh
uv run --project tools/benchmark_investigator pytest tools/benchmark_investigator/tests
uv run --project tools/benchmark_investigator ruff check tools/benchmark_investigator
uv run --project tools/benchmark_investigator ruff format --check tools/benchmark_investigator
```

Tests cover configuration/lineage validation, deterministic summaries, depth-zero
queries, missing profiles, nonzero exits, external kills, immutable artifacts,
source traversal/symlinks, bounded scheduling, 10- and 15-run campaigns, resume, and the
Codex command/schema contract. Actual live validation artifacts are kept under
`.scratch/benchmark-investigator/` and are not committed.

For source quantifier mappings, per-rule work counters, and filtered queries, see
[Quantifier profiling](QUANTIFIER_PROFILING.md). This provenance checkpoint does not
change instantiation search or selection.
