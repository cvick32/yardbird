# LLM-guided instantiation

`--policy llm-one-shot` asks an LLM to choose an array axiom and all of its
bindings together. The default is one complete proposal in one inference call
per abstract countermodel. Yardbird constructs the formula itself and accepts
it only if it is installable, new, and evaluates to known false in that model.
Accepted instances use the existing selection and full-unroll installation path.
Failure or abstention yields to ordinary refinement; neither establishes a real
counterexample or a proof.

This first implementation supports VMT inputs with Z3 and Int-indexed,
Int-valued arrays, matching the JEV experiment. Use `--theory auto` (default) or
`--theory array`. As with JEV, the plan owns array abstraction and leaves input
quantifiers to the solver. Other array sorts cause snapshot capture to skip
inference and use ordinary refinement. Eager seeding, countermodel tracing,
auxiliary synthesis, and prefer-axioms cannot be combined with this policy.

## Running

Choose an explicit provider model ID supported by your account. The model must
support that provider's structured JSON output. Yardbird does not resolve model
aliases or substitute a different model. For comparisons, pin a model version
when the provider offers one; both requested and returned model names are logged.

Inspect the complete OpenAI request without a key or any inference calls:

```bash
cargo run --release -- -f examples/array/array_copy.vmt -d 3 \
  --policy llm-one-shot --llm-provider openai \
  --llm-model YOUR_MODEL_ID --llm-dry-run \
  --llm-log /tmp/yardbird-llm-dry-run.jsonl --json-output
```

For live OpenAI inference, configure `OPENAI_API_KEY` in the environment, remove
`--llm-dry-run`, and choose a new log path. The adapter uses the Responses API.
If supported by the chosen model, add `--llm-reasoning-effort high`.

For Anthropic, configure `ANTHROPIC_API_KEY` and select the Messages adapter:

```bash
cargo run --release -- -f examples/array/array_copy.vmt -d 3 \
  --policy llm-one-shot --llm-provider anthropic \
  --llm-model YOUR_MODEL_ID --llm-log /tmp/yardbird-anthropic.jsonl \
  --json-output
```

On models supporting adaptive thinking, add `--llm-adaptive-thinking` and
optionally `--llm-reasoning-effort high`. Provider/model support for effort
values varies; unsupported settings are reported as failed requests. Omitted
reasoning settings use provider defaults. Yardbird exposes no solver tools or
other tools to either provider.

## Context and response

Both adapters consume `policy::instantiation::InstantiationSnapshot`: complete
original VMT source, native Z3 model including defaults, declarations, every
eligible ground term, exact array axiom schemas, frame metadata, and installed
instances. No property-based shortlist or model-value pruning is applied.
The prompt prefers property-relevant violated instances, like JEV's
property-directed prompt. For a matched comparison, use JEV's
`--jev-prompt property-directed`.

The provider-specific JSON schema allows one joint proposal or an abstention:

```json
{"proposal":{"axiom_id":"q1","bindings":{"a":"t12","idx":"t7","val":"t19"}}}
```

IDs above are illustrative. The required slots depend on the offered axiom.
`{"proposal":null}` explicitly abstains. Local checks reject missing or extra
slots, unknown IDs, wrong sorts, invented formulas, duplicates, and anything
other than a known-false complete instance. Unknown evaluations are never
accepted. Structured output is a formatting aid, not a trusted validation step.

## Reusable context and prompt caching

Both JEV and the LLM now capture through a run-scoped `InstantiationSession`.
The session assigns each `(expression, sort)` a stable term ID, retains every
currently eligible term, and appends new declarations and terms in immutable
vocabulary blocks. IDs depend on the run's discovery order; compare expressions
and sorts across runs, not bare IDs. Removing a term or declaration rebuilds the
vocabulary prefix without reassigning IDs. Changed source or axiom context also
rebuilds the prefix. Removed IDs cannot resolve against the current snapshot.

The LLM receives ordered JSON content blocks:

1. Complete original VMT, axiom schemas, notation, and other static context.
2. Initial vocabulary followed by immutable additions of declarations and terms.
3. Complete current model, depth/version, installed instances, and retry feedback.

Concatenate the vocabulary arrays and combine the other fields to reconstruct
the shared flat snapshot that JEV uses. All blocks are sent on every request.
No terms are shortlisted, no model defaults are omitted, and no previous models
or LLM answers are accumulated. JEV retains its existing staged request format;
its binding choices use the same stable IDs and full current catalogue.

`--llm-explicit-cache true` is the default. The adapters mark the static block
and the latest three vocabulary blocks (at most four breakpoints), retaining
the prior request's endpoint when vocabulary grows. OpenAI uses explicit-only
caching with the default 30-minute lifetime; Anthropic uses block-level ephemeral
caching with its default 5-minute lifetime. The changing final block is never
marked for a cache write. Retry feedback changes only that final block.

OpenAI explicit controls require a supporting model (GPT-5.6 or later). For an
unsupported model, `--llm-explicit-cache false` omits the cache controls while
preserving the split context and stable IDs. This uses provider defaults; it
does not disable OpenAI's implicit caching. Cache hits depend on provider minimum
prefix lengths, cache availability, and unchanged request settings; the log's
reported cache tokens, rather than prefix sizes, determine the cost estimate.

See the official [OpenAI caching guide](https://developers.openai.com/api/docs/guides/prompt-caching)
and [Anthropic caching guide](https://platform.claude.com/docs/en/build-with-claude/prompt-caching).

## Budgets and retries

| Flag | Default | Meaning |
| --- | --- | --- |
| `--llm-attempts` | 1 | Complete proposals per countermodel, including feedback retries |
| `--llm-timeout-secs` | 120 | Deadline for each HTTP request including body reads |
| `--llm-max-request-bytes` | 2097152 | Maximum serialized request size; larger requests are logged and skipped |
| `--llm-max-output-tokens` | 4096 | Provider output budget, including reasoning/thinking |

Set `--llm-attempts 3` to retry malformed or rejected proposals with compact
feedback on the same frozen model and catalogue. Refusals, incomplete responses,
abstentions, and transport errors end the episode immediately. There are no
hidden transport retries or repair calls. Each subsequent solver model starts
a new episode and gets a fresh attempt budget. There is no aggregate API-call
or dollar budget in this initial policy.

The driver's wall timeout is cooperative: an in-flight discovery episode can
finish after that timeout. Use the request timeout and attempt budget to bound
the additional wait, or an external process deadline for a hard benchmark cap.
Oversized inputs are never silently truncated. This version returns one
candidate per call; candidate-list and batch-installation variants are not yet
implemented.

## API spending

Each response records an estimated USD cost from the provider's actual token
usage, plus the rates and pricing date used. Info-level terminal logs show each
call's cost and the running subtotal. This includes rejected proposals,
abstentions, truncation, and feedback retries; output usage already includes
reasoning/thinking tokens. Totals accumulate across countermodels in one run.
Dry runs and skipped requests make zero calls.

Automatic presets use published standard, global prices as of **2026-10-23**:

| Exact model ID | Input / 1M | Output / 1M | Cache read / 1M | Short write / 1M | Long write / 1M |
| --- | --- | --- | --- | --- | --- |
| `gpt-6-astra` | $10 | $50 | $1 | $12.50 | $25 |
| `claude-sonnet-5-5` | $2 | $10 | $0.10 | $2.50 | $4 |
| `claude-sonnet-5` | $2 | $10 | $0.20 | $2.50 | $4 |
| `claude-sonnet-4-6` | $3 | $15 | $0.30 | $3.75 | $6 |

Sources: [OpenAI pricing](https://developers.openai.com/api/docs/pricing),
[Astra context pricing](https://developers.openai.com/api/docs/models/gpt-6-astra),
and [Anthropic pricing](https://platform.claude.com/docs/en/about-claude/pricing).
Astra prompts exceeding 272,000 input tokens use 2× input/cache prices and 1.5×
output prices for the whole request. OpenAI cache writes use 30-minute or 12-hour
rates; Anthropic uses 5-minute or 1-hour rates. Input, cache reads, and cache writes
are accounted for as disjoint categories despite the providers' different usage
formats. If a cache-write lifetime breakdown is absent, writes use the default
short lifetime; this adapter never requests an extended lifetime.

Inspect the latest cumulative estimate (including while the run is active):

```bash
tail -n 1 /tmp/yardbird-astra-1.jsonl | jq '.run_cost'
```

`estimated_subtotal_usd` sums priced calls. `unknown_cost_calls` counts calls whose
usage or pricing is unavailable, including transport failures that might have
reached the provider. `estimated_total_usd` is null if any call is unknown, so a
partial subtotal is never presented as the complete spend. An empty log means no
recorded discovery episode, not a provider billing report.

Other models, dated model IDs, special service tiers, or account-specific pricing
can use explicit effective USD-per-million rates:

```text
--llm-input-usd-per-million 3 --llm-output-usd-per-million 15
--llm-cached-input-usd-per-million 0.30
--llm-cache-write-usd-per-million 3.75
--llm-long-cache-write-usd-per-million 6
```

These illustrative rates replace the entire preset. Both input and output rates
are required; cache rates are required only if that category has nonzero usage.
Custom rates receive no automatic context or tier multipliers. Unknown returned
model IDs are not guessed from the requested model. Missing usage or a missing
required rate produces an unknown cost, never zero. These are estimates excluding
taxes, credits, and negotiated discounts, not invoices or a spending cap.

## Logs and comparison

`--llm-log` must name a new JSONL file. It is created with exclusive creation,
flushed after each event, and never overwritten. Dry runs still perform ordinary
verification and log requests only when abstract countermodels are encountered.

Events include `request`, `request_skipped`, `response`, `attempt_result`,
`transport_error`, `snapshot_error`, and `episode_end`. Records contain provider
configuration, model version, depth, refinement step, and a run-local query ID.
Responses retain raw provider usage, including any cache/reasoning breakdown,
and the resolved model name. Log schema version 3 retains per-response `cost`
and cumulative `run_cost` from version 2, and changes request content to ordered
JSON blocks with explicit cache controls. The shared snapshot schema is also
version 3, reflecting stable run-scoped IDs. Keys and authorization headers are
not written to the log. Requests contain the full verification source and model.

`accepted_instances` counts proposals passing discovery validation. Discovery
cannot observe the installer, so `installation_status` explicitly reports
`not_observed_by_discovery`. Use the normal profiling/solver results for actual
installation totals. `ordinary_fallback` records the discovery handoff decision.
The policy enables profiling automatically, as JEV does.

For the strict comparison, use LLM defaults and JEV `--policy conditional-binding
--jev-prompt property-directed --jev-attempts 5 --jev-candidates 10 --jev-batch
--jev-beam-width 3 --jev-timeout-secs 2`, adding `--no-guided-fallback` to both
methods. JEV selects an axiom, then bindings conditioned on retained prefixes;
the LLM makes one joint proposal. These methods have different inference budgets.
Report calls, usage, latency, validation outcomes, fallback use, and verification
results separately. End-to-end runs can reach different subsequent models.
JEV's `--policy one-shot` remains available as a separate ablation.

## Implementation and verification

- `src/policy/llm/options.rs`: CLI and serialized experiment configuration.
- `src/policy/llm/protocol.rs`: joint output schema, provider requests, response decoding.
- `src/policy/llm/cost.rs`: usage normalization, dated pricing, and cumulative spending.
- `src/policy/llm/client.rs`: bounded HTTP transport, provider authentication, no redirects/retries.
- `src/policy/llm/mod.rs`: discovery episodes, feedback, logging, and proof-plan construction.
- `src/policy/instantiation/`: shared session, stable IDs, immutable vocabulary blocks, exact proposal resolution, and validation.

Tests use injected responses and real Z3 sessions, with no provider credentials
or paid calls:

```bash
cargo test -p yardbird --lib policy::
cargo clippy -p yardbird --lib --tests -- -D warnings
```

The wire formats follow the official
[OpenAI structured-output documentation](https://developers.openai.com/api/docs/guides/structured-outputs?api-mode=responses)
and [Anthropic structured-output documentation](https://platform.claude.com/docs/en/build-with-claude/structured-outputs).
Reasoning controls follow the
[OpenAI reasoning guide](https://developers.openai.com/api/docs/guides/reasoning)
and [Anthropic adaptive-thinking guidance](https://platform.claude.com/docs/en/build-with-claude/extended-thinking#migrating-to-adaptive-thinking).


### Strict comparison mode

Add `--no-guided-fallback` to stop with `NoProgress` when guidance cannot
produce an installable instance. This disables both ordinary Yardbird search
and the driver's concrete-array fallback. It never interprets a failed proposal
as a proof or counterexample. The default retains ordinary fallback.

The four-way Garden experiment, smoke run, AWS secret references, and live
figure commands are documented in `garden/instantiation_comparison.md`.
