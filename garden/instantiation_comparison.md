# Four-way instantiation comparison

`instantiation_comparison.yaml` runs the complete `examples/array` corpus at
depth 50, with a 600-second subprocess wall timeout, one trial, and one worker
per method. `instantiation_comparison_smoke.yaml` uses `array_copy.vmt` and
`array_hybr_sum.vmt`, depth 4, and 120 seconds. Each YAML contains exactly one
configuration for each method:

| Matrix | Configuration |
| --- | --- |
| `jev` | `conditional-binding`, property-directed prompt, `jev-latest`, 5 attempts, 10 candidates, beam width 3, batching, 2-second request timeout |
| `openai` | `llm-one-shot`, `gpt-6-astra`, one complete-proposal attempt, explicit prompt caching |
| `yardbird` | Frozen best abstract configuration from the August 31 depth-50 ablation: BMC cost, source-then-full, prefer-source ranker, 16 winners |
| `z3` | Concrete Z3 arrays |

All use Z3, assumption-based property checks, and full-unroll installation.
The abstract baseline is a fixed configuration, not a per-benchmark oracle.
JEV and the LLM receive the same complete source/model/term context and use the
same validation and installation machinery. JEV uses the established conditional
baseline: select an axiom, then select bindings sequentially conditioned on the
retained prefixes. Its attempt and candidate budgets apply per countermodel;
batching installs all distinct verified violations within the candidate budget.
The LLM jointly selects the axiom and all bindings in one request. Their API
budgets differ; both have the same benchmark wall timeout, and embedded API
accounting records the actual calls and estimated costs. Model response names
and complete options are retained in the logs.

The separate JEV `--policy one-shot` implementation and tests remain available
for ablations. Earlier smoke results using that policy do not evaluate this
conditional-binding baseline; use fresh output paths when rerunning.

Both guided methods set `no_guided_fallback: true`. Their scheduling policy
stops with `NoProgress` on exhaustion, before ordinary matching, vocabulary
expansion, or concrete-array counterexample validation. Successful proposals
still pass shared model-violation validation and installation. Without this
flag, the existing ordinary fallback remains the default. For standalone runs,
add `--no-guided-fallback` to either guided policy's command.

`Success` means completion of the requested BMC bound, not an unbounded proof.
`NoProgress` is inconclusive. This single-trial comparison does not estimate
variance, and the corpus includes the development/smoke examples; it is not a
held-out evaluation. Change the cohort explicitly before making held-out claims.

## Local smoke and full runs

Set `JEV_API_KEY` and `OPENAI_API_KEY` in the environment or the ignored root
`.env` file. Garden preflights both providers before running benchmarks.

```sh
cargo build --release -p yardbird -p garden
target/release/garden --config garden/instantiation_comparison_smoke.yaml \
  --output /tmp/instantiation-smoke.json --profile
paper-graphics/.venv/bin/python paper-graphics/guided_comparison.py \
  /tmp/instantiation-smoke.json --output-dir /tmp/instantiation-smoke-figures
```

Use a new output basename for every run. Garden saves API logs in the adjacent
`instantiation-smoke.api/` directory and refuses to reuse that directory.
`--guided-log-root NEW_DIRECTORY` overrides the log location. Guided benchmark
attempts are never silently retried by Garden, including timeouts and errors.
Provider-level attempt budgets remain explicit in YAML. Logs survive hard
timeouts and include unresolved requests whose eventual charge is unknown.

For a free pipeline check, add `--guided-dry-run`. This generates the full
requests, then stops guided methods with `NoProgress`; figures are marked
**DRY RUN** and must not be used as model evaluation results.

For the full local evaluation, replace the config with
`garden/instantiation_comparison.yaml` and choose a fresh output. No full
evaluation is launched by these setup instructions.

## Figures while the evaluation runs

Garden atomically rewrites results after every completed benchmark, retaining
the full planned cohort in metadata. Re-run the figure command at any point.
Pending work is shown separately from failures. The script exports CSV/JSON
tables and six PDF/PNG figure pairs:

- outcomes, including pending, timeout, and no-progress counts;
- end-to-end runtime and installed-instantiation cactus plots;
- completed-depth progress;
- API spend, inference latency, and episode acceptance;
- OpenAI prompt-cache token usage.

Each completed Garden strategy result now embeds `api_usage`. This includes
`api_calls`, token totals, `api_seconds`, `estimated_subtotal_usd`,
nullable `estimated_total_usd`, `unknown_cost_calls`, `unresolved_requests`,
resolved model names, and episode/acceptance/fallback counts. It is populated
after success, no-progress, errors, and hard timeouts. Non-API baselines report
zero API cost. Missing or damaged evidence leaves the total unknown while
preserving the known subtotal. A verified run with only UNSAT checks needs no
API calls and can legitimately have no JSONL file.

The comparison script treats embedded accounting as authoritative, including
unknown totals: completed results can be plotted from `results.json` alone.
JSONL remains the detailed audit trail and the compatibility source for old
results and in-flight work. `fallback_episodes` counts handoffs to ordinary
search, not the number of lemmas installed by that search.

Tables include calls, tokens, resolved model names, accepted episodes,
cost/latency per accepted episode, and incomplete cost evidence. Cost totals
sum per-call records once; cumulative `run_cost` fields are not added together.
Unknown-cost calls, killed/in-flight requests, and missing logs are not free.
Latency for an unfinished request is a lower bound until its response arrives.
Keep raw JSON and JSONL files with the figures for auditability.

The existing paper figure generator also accepts these Garden results for
paired runtime/solver-stat plots and LaTeX tables:

```sh
paper-graphics/.venv/bin/python paper-graphics/main.py \
  /tmp/instantiation-smoke.json --figures --output-dir /tmp/instantiation-smoke-tex
```

Use one trial at a time. The new comparison script rejects duplicate
method/benchmark observations rather than choosing a favorable result.

## AWS credentials and reproducibility

`main_eval.py` delegates to `yardbird_eval/aws_backend.py`. API keys are not
forwarded from the controller's environment. Provision the two keys as SSM
**SecureString** parameters in the worker region, using the AWS console or a
secure provisioning process. Never put key values in YAML, CLI arguments,
Terraform variables/state, or user-data. Example parameter names are
`/yardbird/openai-api-key` and `/yardbird/jev-api-key`.

Add their exact ARNs to Terraform's `api_key_parameter_arns` list and apply the
IAM change through the normal infrastructure workflow. For parameters encrypted
with a customer-managed key, also set `api_key_kms_key_arns` and authorize the
worker role in that key's policy. The new IAM policy grants `ssm:GetParameter`
only for the listed parameters; optional KMS decrypt is restricted to SSM.

Workers fetch credentials after switching to the Ubuntu user, via their
instance role, and export them only for the benchmark process tree. Fetch
failure stops the worker. User-data contains parameter references, never key
values. Shell tracing must remain disabled. API logs contain source programs,
models, and responses; keep the results bucket appropriately private.

Commit and push the changes before launch: workers clone the repository.
Use a pushed commit SHA with `--git-ref` for reproducibility; omitting it retains
the existing latest-main behavior. Model aliases can change independently of
the code commit, so retain resolved response IDs.

```sh
python3 main_eval.py --env aws --aws-account personal \
  --config garden/instantiation_comparison.yaml \
  --benchmark-type jev --benchmark-type openai \
  --benchmark-type yardbird --benchmark-type z3 \
  --openai-api-key-parameter /yardbird/openai-api-key \
  --jev-api-key-parameter /yardbird/jev-api-key \
  --git-ref PUSHED_COMMIT_SHA --profile --name instantiation-comparison
```

This launches one worker per matrix. Use the smoke YAML first to validate IAM
and network access in AWS. Local smoke does not validate an AWS deployment.

Workers upload a separate `partial.json` and API logs every 15 seconds. A
partial snapshot does not mark the run complete. To refresh local evidence:

```sh
python3 main_eval.py --run-id RUN_ID --sync-partial
paper-graphics/.venv/bin/python paper-graphics/guided_comparison.py \
  benchmark_results/main_eval/RUN_ID/run.json --output-dir /tmp/comparison-figures
```

Final downloads refresh any earlier partial result and preserve API logs next
to each raw results file. The comparison script accepts the run manifest or
all four raw result paths. Never combine a manifest and the same raw files
from another copy of that trial.


## JEV working with ordinary Yardbird search

Use `instantiation_comparison_fallback.yaml` (full) or
`instantiation_comparison_fallback_smoke.yaml` (local smoke) to add a fifth
matrix, `jev-fallback`. The original four-way configurations remain unchanged.
The new matrix has the same conditional-binding policy, model, prompt, attempt
and candidate budgets, batching, beam width, depth and timeouts as strict `jev`;
only `no_guided_fallback` is false.

JEV gets the first opportunity for each solver model. If it cannot produce an
installable violated instance, existing ordinary Yardbird search continues.
After refinement produces a new model, JEV gets another opportunity. This
retains the existing ordinary fallback policy (including its concrete
counterexample-validation behavior), not the separate countermodel-guided
policy or the 16-winner best-abstract baseline.

```sh
target/release/garden --config garden/instantiation_comparison_fallback_smoke.yaml \
  --output /tmp/instantiation-fallback-smoke.json --profile
paper-graphics/.venv/bin/python paper-graphics/guided_comparison.py \
  /tmp/instantiation-fallback-smoke.json --output-dir /tmp/instantiation-fallback-figures
```

To run only the added method, pass `--matrix jev-fallback`. For AWS, select the
full fallback YAML and add `--benchmark-type jev-fallback` to the launch command.
Both figure generators keep strict JEV and JEV with fallback as separate series.
The API-cost/latency plot includes all three API-backed methods.
