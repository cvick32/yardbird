# LLM-guided instantiation

Yardbird can ask an LLM to pick a theory rule and bind its variables to terms
from an abstract countermodel. Yardbird builds the resulting formula and
checks that it is new, can be installed, and evaluates to false in that model.
It installs selected instances through the usual full-unroll path.

- `--policy llm` asks the model first. By default it makes one call per
  countermodel, then falls back to ordinary refinement if guidance yields no
  usable instance. Existing configs can still use the alias `llm-one-shot`.
- `--policy symbolic-llm` starts with a bounded symbolic search. If that
  search finds nothing to install, the LLM gets a turn and symbolic search
  resumes. An installation sends control back to the solver. Otherwise, the
  next turn keeps the same model, term IDs, rejection feedback, and search
  progress.

Both policies use Z3 with VMT inputs. They support typed arrays, including
Boolean and nested-array values, and rules derived from quantifiers in the
input. `--theory auto` covers both. You can also select `array`, `quantifiers`,
or `array,quantifiers` explicitly. For distributed protocols, use the
`*.encoding.vmt` companion files. Direct lambda guidance is unsupported.

## Run a dry run

From the repository root, pick an exact model ID that supports structured
JSON output on your provider and use a new log filename.

```bash
cargo run --release -- -f examples/array/array_copy.vmt -d 3 \
  --policy llm --llm-provider openai --llm-model YOUR_MODEL_ID \
  --llm-dry-run --llm-log /tmp/yardbird-llm-dry-run.jsonl --json-output
```

A dry run needs no API key. Yardbird runs verification and logs the request
it would send whenever it reaches an abstract countermodel. For a live run,
remove `--llm-dry-run`, set the provider's API key, and use a fresh log path.

| `--llm-provider` | API key | API |
| --- | --- | --- |
| `openai` | `OPENAI_API_KEY` | Responses |
| `anthropic` | `ANTHROPIC_API_KEY` | Messages |
| `bedrock` | `BEDROCK_API_KEY` | OpenAI-compatible Responses |

Use `--llm-reasoning-effort high` on models that support it. Anthropic models
with adaptive thinking also accept `--llm-adaptive-thinking`.

### Amazon Bedrock

Set `BEDROCK_API_KEY` in your environment or the repository's ignored `.env`.
Choose a model that supports Responses and structured JSON on your endpoint.
If Bedrock Runtime requires an inference profile, pass its ID to
`--llm-model`.

Set the region with `--llm-bedrock-region`, or through `BEDROCK_REGION`,
`AWS_REGION`, or `AWS_DEFAULT_REGION`, in that order. Yardbird uses
`https://bedrock-runtime.REGION.amazonaws.com/openai/v1/responses` by default.
If your model requires Mantle, pass the base URL from its model card to
`--llm-bedrock-base-url`, for example
`https://bedrock-mantle.REGION.api.aws/v1`. A base URL takes precedence over
the region settings. Refresh the API key if Bedrock returns an expired-signature
`401 invalid_api_key`. [AWS Responses API guide](https://docs.aws.amazon.com/bedrock/latest/userguide/inference-responses-api.html)

Bedrock uses provider-default caching, and requests set `store=false`. For
cost estimates, supply your Bedrock rates explicitly. In Garden, set
`llm_provider`, `llm_model`, `llm_bedrock_region`, and, if needed,
`llm_bedrock_base_url` inside the `llm` configuration. Use a separate named
parameter matrix for each model you want to compare.

## What the model sees

The request includes the original VMT source, the complete current Z3 model
including defaults, declarations, eligible ground terms, rule schemas, frame
information, and installed instances. Rules come from built-in array axioms
or the input's registered quantifier lowering plan. Rule schemas describe
which variables need bindings and how Yardbird derives any witnesses.

The response is a single proposal using the offered rule and term IDs. For
example, a rule with slots `a`, `idx`, and `val` might receive:

```json
{"proposal":{"axiom_id":"q1","bindings":{"a":"t12","idx":"t7","val":"t19"}}}
```

Use `{"proposal":null}` to abstain. Yardbird checks the slot names, term IDs,
and sorts before it builds and validates the formula. Each term ID identifies
an expression and sort within one run. Compare expressions and sorts when
comparing across runs. JEV uses the same term catalogue and stable IDs.

Requests group the source and rules, vocabulary, and changing model state
into separate blocks. Explicit caching is on by default for OpenAI and
Anthropic. Yardbird marks the static context and up to three vocabulary blocks
for caching. Use `--llm-explicit-cache false` to use provider defaults, for
example with a model that lacks explicit cache controls.

## Search limits

| Flag | Default | What it limits |
| --- | --- | --- |
| `--llm-attempts` | 1 | Calls per LLM turn, including feedback retries |
| `--llm-max-calls-per-model` | 8 | Calls for one solver model |
| `--llm-max-calls` | 100 | Calls across the whole run |
| `--llm-timeout-secs` | 120 | Seconds per HTTP request, including reading the response |
| `--llm-max-request-bytes` | 2097152 | Serialized request size |
| `--llm-max-output-tokens` | 4096 | Output tokens, including reasoning |
| `--symbolic-operations` | 8 | Symbolic operations before an LLM turn |
| `--symbolic-match-work` | 128 | Match or page work per symbolic operation |
| `--symbolic-dependency-work` | 128 | Dependency work per symbolic operation |
| `--symbolic-vocabulary-work` | 64 | Term-construction attempts per vocabulary operation |

Set `--llm-attempts 3` to retry rejected or malformed proposals with feedback
from the same solver model. Refusals, incomplete responses, abstentions, and
transport errors end the current turn. In `symbolic-llm`, abstentions and
invalid bindings can be revisited in a later turn. Provider and transport
failures, refusals, and incomplete responses disable further hybrid inference
for the run. Rejected calls and transport failures count toward the call
limits. Yardbird skips oversized requests. The driver checks its wall
timeout between operations, so an active request can finish after that
deadline.

With `llm`, reaching a call limit hands off to ordinary refinement by
default. Add `--no-guided-fallback` for a strict comparison. This disables
ordinary search and the concrete-array fallback, so failed guidance ends
with `NoProgress`. The hybrid policy already disables concrete validation,
returns `NoProgress` when it reaches a call limit, and does not accept
`--no-guided-fallback`.

## Read the log

`--llm-log` creates a new JSONL file and flushes each event as it happens.
The log includes requests, responses, validation outcomes, and errors.
Request records include the full verification source and model. Response
records include the returned model ID, token usage, and an estimated cost
when usage and rates are available.

```bash
tail -n 1 /tmp/yardbird-llm-dry-run.jsonl | jq '.run_cost'
```

For live runs, `estimated_subtotal_usd` sums calls with known costs.
`estimated_total_usd` is null if `unknown_cost_calls` is greater than zero.
Yardbird has dated rate presets for some exact model IDs in [cost.rs](cost.rs).
To supply your own rates, set both `--llm-input-usd-per-million` and
`--llm-output-usd-per-million`, plus any rates for cache usage that your
provider reports (`--llm-cached-input-usd-per-million`,
`--llm-cache-write-usd-per-million`, and
`--llm-long-cache-write-usd-per-million`).

`accepted_instances` counts proposals that passed discovery validation.
Check profiling or solver results for installation totals. For the Garden
experiment setup, JEV settings, and reproduction commands, see the
[instantiation comparison guide](../../../garden/instantiation_comparison.md).

## Development

Start with [options.rs](options.rs) for CLI settings, [protocol.rs](protocol.rs)
for request and response formats, [client.rs](client.rs) for HTTP, and
[mod.rs](mod.rs) for the discovery loop. The tests use injected responses and
local Z3 sessions, so they need no provider credentials.

```bash
cargo test -p yardbird --lib policy::
cargo clippy -p yardbird --lib --tests -- -D warnings
```
