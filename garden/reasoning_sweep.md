# Reasoning-effort sweep

`reasoning_sweep.yaml` is an end-to-end Garden experiment using the existing
joint-proposal interface. `reasoning_sweep_smoke.yaml` has the same settings and
matrix names, but only the two prompt-development examples at depth 4.

| Matrices | Model / reference |
| --- | --- |
| `astra-low`, `astra-high`, `astra-max` | `gpt-6-astra`, explicit effort |
| `luna-low`, `luna-medium`, `luna-high` | `gpt-6-luna`, cheaper-model comparison |
| `jev` | `jev-1.14.0`, historical conditional-binding configuration |
| `yardbird` | Abstract BMC cost, term-cost ranker, one winner per group |
| `z3` | Native Z3 arrays |
| `random-1`, `random-1000` | Uniform random proposals, at most 1 or 1,000 samples per countermodel |

The full configuration selects every VMT under `examples/array` (189 at setup),
depth 50 (frames 0–49), a 120-second subprocess wall timeout, and one worker.
Every abstract method uses source-then-full vocabulary, assumption property
checks, term-cost ranking, one winner per group, and full-unroll installation.
The baseline matches the revised paper, rather than the historical source-ranked
16-winner baseline. The smoke cohort is `array_copy` and `array_hybr_sum`.

All LLM arms use one joint proposal per countermodel, explicit prompt caching,
a 120-second request timeout, and a common 32,768-token output ceiling including
reasoning. No reasoning mode or service-tier override is sent. Ordinary fallback
is disabled consistently: a failed guided refinement is an inconclusive
`NoProgress`, not a counterexample. Jev retains five attempts, ten candidates,
beam width three, batching, and a two-second request timeout; it is a reference,
not an equal-inference-budget control.

Effort is an adaptive control, not a fixed token budget. Retain actual reasoning
tokens and incomplete-response reasons from raw JSONL. The larger output ceiling
is a pilot choice, not evidence that truncation cannot occur. It differs from the
historical Astra ceiling of 4,096 tokens, so compare newly repeated configurations
for causal effort claims. Requested and resolved model IDs are logged; the OpenAI
model names are not immutable dated snapshots. The explicit Jev version avoids
`jev-latest`; an offline check cannot establish continued provider availability.

Model settings and standard/global pricing were checked on 2026-10-31:
[Astra](https://developers.openai.com/api/docs/models/gpt-6-astra),
[Luna](https://developers.openai.com/api/docs/models/gpt-6-luna), and
[reasoning](https://developers.openai.com/api/docs/guides/reasoning).
Luna's pricing preset includes cache reads/writes and the >272k-input-token
multiplier. Unknown returned model versions or unsupported billing tiers remain
unknown-cost records. API estimates are not spending caps or invoices.

## Rough Astra budget (2026-11-01)

The selected Astra arms are low, high, and max. The historical 189-benchmark
Astra run recorded 917 requests and $53.56 known spend, including failed runs;
seven requests had unresolved cost. Of the known spend, $47.08 was input/cache
and $6.48 was output. The 910 completed responses averaged 142 output tokens,
including 100 reasoning tokens. Historical effort was not explicitly set.

At current standard pricing ($50 per million output tokens), holding request
counts and input/cache usage fixed gives these **three-arm total** scenarios:

| Additional output tokens per request in each of high and max; low unchanged | API total |
| --- | ---: |
| 0 (historical usage repeated three times) | $161 |
| 1,000 | $252 |
| 4,000 | $527 |
| 8,000 | $894 |

These are sensitivity calculations, not measured predictions of effort levels.
Different decisions, cache behavior, and the 120-second cutoff can change request
counts and spending. The new 32,768-token ceiling also permits more reasoning
than the old 4,096-token ceiling. Roughly $500 is a provisional planning allowance
for one Astra-only sweep, not an enforced cap; a small live pilot should refine
it. Three repetitions multiply the selected scenario by three. Luna, Jev, and
hosting are excluded; rerunning Jev at historical usage adds about $30 per trial.

Sources: the paper's `figures/evaluation-data.json`, the retained Astra JSONL
usage records, and [current Astra pricing](https://developers.openai.com/api/docs/models/gpt-6-astra).

## Build and validate without inference

Run from the repository root. Build both binaries together; Garden invokes the
Yardbird executable beside itself.

```sh
cargo build --release -p yardbird -p garden
target/release/garden --config garden/reasoning_sweep_smoke.yaml \
  --guided-dry-run --profile --output /tmp/reasoning-sweep-offline.json
```

Use a fresh output basename for every invocation. Garden retains JSONL in the
adjacent `.api` directory and refuses to reuse it. `--guided-dry-run` requires no
provider keys and makes no inference calls. API-guided cases should stop with
`NoProgress` after logging their first request; ordinary and random references
still execute locally. Random cases are real samples, not dry-run results.
Inspect the JSONL `request.model`, `request.reasoning.effort`, and
`request.max_output_tokens` to verify every arm. This validates wiring, not
provider access or decision quality.

## Live pilot and full trial

These commands make paid calls. Set `OPENAI_API_KEY` and, when selecting Jev,
`JEV_API_KEY` using the existing environment or ignored `.env` setup. To pilot
only one arm without requiring a Jev credential:

```sh
target/release/garden --config garden/reasoning_sweep_smoke.yaml \
  --matrix astra-low --profile --output /tmp/reasoning-astra-low-pilot.json
```

After checking provider support and output truncation, a full single trial is:

```sh
target/release/garden --config garden/reasoning_sweep.yaml \
  --profile --output /tmp/reasoning-sweep-trial-1.json
```

`--matrix` accepts any table entry, so individual arms can be scheduled or
repeated independently. `--limit 40 --sample-seed 20261031` gives the same sampled
benchmark cohort for every arm; it is not a family-stratified or active-only
sample. The full corpus includes the two development examples and benchmarks
requiring no refinement. Preserve these labels in analysis rather than calling
the entire corpus held out. Freeze any development/evaluation split separately.

`retry_count: 1` means one execution, **not three repeated trials**. Guided
failures are never silently retried. For three trials on the same host with
deterministically shuffled matrix order and separate outputs, the following
optional launcher uses only the Python standard library. It makes paid calls:

```sh
python3 - <<'PY'
import json
import platform
import random
import subprocess
from pathlib import Path

root = Path('/tmp/reasoning-sweep-repeated')
root.mkdir(exist_ok=False)
matrices = ['astra-low', 'astra-high', 'astra-max',
            'luna-low', 'luna-medium', 'luna-high', 'jev', 'yardbird', 'z3',
            'random-1', 'random-1000']
orders = []
for trial in range(1, 4):
    order = matrices.copy()
    random.Random(20261031 + trial).shuffle(order)
    orders.append(order)
(root / 'schedule.json').write_text(json.dumps({
    'host': platform.node(), 'platform': platform.platform(), 'orders': orders,
}, indent=2))
for trial, order in enumerate(orders, 1):
    directory = root / f'trial-{trial}'
    directory.mkdir()
    for matrix in order:
        subprocess.run(['target/release/garden', '--config', 'garden/reasoning_sweep.yaml',
                        '--matrix', matrix, '--profile', '--random-seed', str(trial - 1),
                        '--output', str(directory / f'{matrix}.json')], check=True)
PY
```

Before live collection, retain the commit, working-tree changes, config and
binary hashes, host CPU/memory/OS, and solver version alongside the schedule.
Keep service conditions consistent and report actual cache usage: randomizing
method order does not itself guarantee cold caches. Report all outcomes and
failed-run spending, with uncertainty grouped by benchmark and trial.

## AWS and result analysis

The existing `main_eval.py` launcher accepts these matrix names via repeated
`--benchmark-type` options. For example, after committing and pushing the config:

```sh
python3 main_eval.py --env aws --aws-account personal \
  --config garden/reasoning_sweep.yaml \
  --benchmark-type astra-low --benchmark-type astra-high --benchmark-type astra-max \
  --benchmark-type luna-low --benchmark-type luna-medium --benchmark-type luna-high \
  --benchmark-type jev --benchmark-type yardbird --benchmark-type z3 \
  --benchmark-type random-1 --benchmark-type random-1000 \
  --openai-api-key-parameter /yardbird/openai-api-key \
  --jev-api-key-parameter /yardbird/jev-api-key \
  --git-ref PUSHED_COMMIT_SHA --profile --name reasoning-sweep-trial-1
```

This launches one worker per selected matrix, not a shared physical host. Use
the local sequential recipe on a documented machine for same-host comparisons.
See `instantiation_comparison.md` for the existing SSM/IAM setup.

Garden's raw JSON retains distinct `run_name`, model/effort options, outcomes,
profiling, and embedded API usage for each arm. JSONL retains reasoning-token
breakdowns and raw responses. Keep trials separate and retain interrupted
requests as unresolved charges. The old `guided_comparison.py` and
`guided_tables.py` are specialized for the original four/five methods and do not
support these new names; do not use them to summarize this sweep. A dedicated
effort-frontier analysis is subsequent work.

These files configure end-to-end trajectories. They do not implement the
proposed fixed-countermodel replay experiment, adaptive effort, or a held-out
selection protocol.

## Random controls

`--policy random-instantiation` uses the exact shared snapshot catalogue and
array-axiom schemas as the LLM and Jev policies. It selects an eligible axiom
uniformly, then independently selects each binding uniformly from all catalogue
terms of the required sort. Sampling is with replacement: repeated tuples and
previously installed instances consume the budget too. This distribution gives
each axiom equal mass; it is not uniform over the union of all Cartesian tuples.
No property relevance, model values, e-class representatives, cost, or earlier
validation feedback influences sampling. The common validator checks the whole
formula, novelty, and installability; only its first accepted instance proceeds
to ordinary selection and full-unroll installation.

`random-1` matches Astra's one-proposal budget. `random-1000` measures a larger
budget for cheap local search; it stops early at the first accepted tuple. Both
stop inconclusively when their budget is exhausted because the YAML disables
ordinary fallback. Standalone use can omit `--no-guided-fallback` to allow the
usual heuristic handoff. Neither budget exhaustion nor an undetermined model
evaluation establishes a proof or a counterexample. Support is the same initial
Z3/Int-indexed/Int-valued array domain as the existing AI proposal interface.

Run a free smoke comparison, with fresh output names:

```sh
target/release/garden --config garden/reasoning_sweep_smoke.yaml \
  --matrix random-1 --random-seed 0 --profile --output /tmp/random-1-seed0.json
target/release/garden --config garden/reasoning_sweep_smoke.yaml \
  --matrix random-1000 --random-seed 0 --profile --output /tmp/random-1000-seed0.json
```

For a standalone input:

```sh
target/release/yardbird -f examples/array/array_copy.vmt -d 4 \
  --policy random-instantiation --random-seed 0 --random-samples 1000 \
  --random-log /tmp/random-copy-seed0.jsonl --no-guided-fallback --json-output
```

Garden allocates per-case random logs in its existing `.api` directory, but
reports zero API calls and zero API spend. Logs contain one complete snapshot
per episode, the sampling distribution and seed, every attempted tuple and its
validation outcome, and total samples at termination. Snapshot capture and
logging remain part of wall time. Logs are created exclusively and survive
timeouts; incomplete final episodes must not be counted as completed failures.

`--random-seed` on Garden overrides the random matrices only; `--sample-seed`
controls benchmark selection and is unrelated. Each benchmark resets the PRNG
to the configured seed. The repeated-trial recipe uses proposal seeds 0, 1, 2.
The AWS wrapper currently takes sampler seeds from YAML, so use explicitly
versioned configs to vary seeds there. Reproducibility requires the same build,
locked `rand` version, catalogue order, and solver trajectory, not just a seed.

Report first-proposal acceptance separately from success after up to 1,000
attempts. Stop-on-success logs are not a fixed-size random sample per state;
their pooled acceptance rate does not estimate an equally weighted state-level
base rate. End-to-end random and AI runs also encounter different subsequent
countermodels. A paired fixed-snapshot study is still needed for that claim.
