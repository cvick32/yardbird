# Local array baseline

Build the current checkout, then run all VMT files recursively under
`examples/array/` (currently 189):

```bash
cargo build --profile quick --bin yardbird
python3 tools/decision_model/run_array_baseline.py \
  --baseline jev --depth 20 \
  --output benchmark_results/local_eval/array-jev-depth20
```

This runs Yardbird locally and calls the Jev API using Yardbird's usual
`JEV_API_KEY` environment/`.env` loading. The baseline matches the latest production
experiment: conditional binding, property-directed prompt, native model, full VMT,
batching, 10 candidates, beam width 3, 5 attempts, and a 2-second API timeout.
Ordinary refinement remains enabled as fallback. No experimental model-reading
formats or prompts are used. The script does not build or change the executable.

For an entirely local, non-Jev baseline, use `--baseline yardbird`; this selects
the abstract strategy with BMC cost and Z3. Give each baseline a distinct output
directory. `--binary` can select another built executable.

`--depth 20` passes `-d 20`, checking frames 0–19. This is bounded checking, not an
inductive proof. Defaults are sequential execution, a 120-second cooperative
budget per benchmark, and 10 additional seconds before terminating the process
group (with up to 2 seconds for graceful shutdown). Override `--timeout-secs` and
`--grace-secs` if needed. All inputs are included, including those the Jev policy
may not support; their errors/fallbacks are part of the results. There is no retry.

The output contains:

- `manifest.json`: exact commands, configuration, binary/script/input hashes, and
  Git commit. No environment variables or API key are recorded.
- `results.csv` and `results.json`: one row per benchmark, refreshed after each run.
- `summary.json`: outcome counts, incomplete/failed cases and their errors,
  aggregate Jev failure reasons, verified/true/duplicate candidate counts, and
  known estimated query cost plus unknown-cost query counts.
- `cases/NNN-name/`: stdout `result.json`, `stderr.log`, `progress.json`, exact
  command, case summary, and (for Jev) `jev.jsonl` and `jev-summary.json`.

`bounded_complete` requires structured progress through the requested depth;
exit code zero alone is insufficient. `installed_schemas` counts the result's
reported `used_instances`; `indexed_assertions` is the reported frame assertion
count. `jev_fallback_requested_episodes` records requests to resume ordinary
search, not a count of installed fallback instances. Full profiles preserve
installation and timing details for deeper attribution. A hard kill can leave
stdout incomplete; the separate progress checkpoint records the latest progress.

Preview commands without launching Yardbird, calling Jev, or creating output:

```bash
python3 tools/decision_model/run_array_baseline.py --baseline jev --dry-run
```

Resume with the same flags and `--output`, adding `--resume`. Completed summaries,
including failures and interruptions, are skipped. An unfinished case directory
without a summary is marked `interrupted_unrecorded` and retained rather than
silently requerying Jev. Binary, script, input, or configuration changes require
a new output directory. `--limit N` selects the first N sorted inputs for a small
run; omit it for the entire suite.

Test the runner and trace summarizer without running benchmarks:

```bash
python3 -m unittest discover -s tools/decision_model -p 'test_*.py' -v
```

### Shared vocabulary identity

JEV and `llm-one-shot` capture through the same run-scoped instantiation session.
Shared snapshot schema version 3 assigns stable IDs to `(expression, sort)` pairs
as terms appear. IDs are never reassigned within a run, but only the current
catalogue is eligible. Different runs can discover terms in different orders;
compare expressions and sorts when aligning their logs. JEV continues to send a
flat snapshot and full binding domains. The LLM serializes equivalent static,
append-only vocabulary, and current-model blocks for prompt caching; see
[LLM context caching](../../src/policy/llm/README.md#reusable-context-and-prompt-caching).
