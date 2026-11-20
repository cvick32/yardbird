# Agent interaction with Yardbird

| Mode | Who proposes instances | When the solver runs |
| --- | --- | --- |
| [Asynchronous advice](#asynchronous-advice) | Bedrock supplies hints alongside the selected Yardbird policy | Native refinement continues during inference. |
| [One-shot batches](#one-shot-instantiation) | Bedrock submits batches of ground substitutions | Yardbird checks each batch and can return feedback for another round. |

## Asynchronous advice

The agent supplies instantiation hints while Yardbird keeps running its normal
search with the selected policy. For LLM batches checked without native search,
use [one-shot mode](#one-shot-instantiation). Each async `instantiate` binding
accepts a pinned term ID or a ground SMT-LIB term over the pinned declarations.
A proposal can mix both forms.

For a paired async experiment, `--agent-start-model N --agent-stall-secs 0`
starts advice at the first eligible SAT boundary at or after model N.
Add `--agent-binder-context` to show source quantifiers, original slot names,
action names where indexed, ground capture tuples, and bindings recovered from
installed ordinary and witness instances. Witness entries link to the same source context.

### Run German

```sh
./target/release/yardbird \
  -f examples/distributed_protocols/german/german.encoding.vmt \
  --policy german-fast -d 20 --wall-timeout-secs 500 \
  --agent bedrock
```

Uses `BEDROCK_API_KEY` from the environment or `.env` and the bundled
[Bedrock configuration](bedrock-config.json). Calls are paid; there is no default
call or dollar cap. Set `--agent-max-calls N` to limit calls.

By default, advice starts after five seconds at an unresolved depth. Yardbird
checks for requests and replies at SAT boundaries, so long solver/search steps
can delay dispatch. Native search continues while the model responds. Hints are
validated against the current state before entering normal selection and
installation; the agent cannot stop the verifier or declare success.

### Options

| Flag | Use |
| --- | --- |
| `--agent-stall-secs N` | Change the five-second threshold; 0 starts immediately. |
| `--agent-trigger adaptive` | Ask the LLM whether to keep searching or offer hints. These assessments also count as paid calls. |
| `--agent-timeout-secs N` | Set the timeout for each provider call. |
| `--agent-config FILE` | Override the bundled provider configuration. |
| `--agent-log FILE` | Choose a new log file; existing files are never overwritten. |
| `--agent-dry-run` | Capture the first eligible request without calling Bedrock, then continue native search. |

For an immediate offline capture, combine `--agent-dry-run` with
`--agent-stall-secs 0`. Use `--help` for other limits.

### Results and comparisons

The console shows advice, public rationales, proposed formulas and installation
outcomes. Full transcripts go to `.yardbird/runs/<run>/agent.jsonl`; the path is
printed at startup. Yardbird's normal result determines verification success.
Provider failures disable advice and leave native verification running.

Omit `--agent bedrock` for the native baseline. Use `--agent none` to measure
the agent attachment/polling overhead without snapshots or provider calls.
Use the same input, policy, depth and wall budget when comparing runs.

### Offline tests

```sh
cargo test --lib agent_interaction::tests
cargo test --test agent_interaction_tests
```

## One-shot instantiation

Ask Bedrock for a batch of instantiations, check it, and send solver feedback for
another batch until every bound closes or the wall timeout expires. Accepted
instances accumulate; there is no symbolic refinement or fallback.

```sh
./target/release/yardbird \
  -f examples/distributed_protocols/german/german.encoding.vmt \
  --policy german-fast -d 20 --wall-timeout-secs 500 \
  --agent bedrock --one-shot --agent-timeout-secs 500
```

This uses the existing Bedrock configuration and `BEDROCK_API_KEY`. Each round
is a paid call; there is no default call cap. Add `--agent-max-calls 1` for the
original single-call experiment, or set another cap. `--agent-dry-run` saves
the first request without a call. The wall budget covers all rounds and checks.

### Prompt and response

The model receives the source, prepared abstraction, declarations, trusted
instantiation schemas and target depths. The first request has no solver model;
retries include closed/unresolved bounds, accepted formulas, the first remaining
countermodel and the previous submission. No native search results are supplied.
Each `submit_instantiations` response contains a public
rationale and a list of schema IDs with typed, ground SMT-LIB substitutions.
Yardbird checks each proposal and reports rejected entries by index.

By default, each concrete instance becomes a temporal schema through Yardbird's
normal frame normalization and installation policy. For example, `A@4` and `i@5`
become `A+0` and `i+1` with the same origin. With `german-fast`, native full-unroll
replay instantiates the pattern at every eligible depth. Shifted duplicates are
stored once. This preserves relative distances; it does not enumerate new index
combinations. Use `--one-shot-placement exact` for the previous exact-frame ablation.

The default [prompt](one_shot/prompt.md) is bundled into the binary. Override it without
rebuilding with `--one-shot-prompt path/to/prompt.md`; the exact text is logged.
`--one-shot-output-tokens N` changes the default 32,768-token response budget.
There is no proposal-count cap. Valid proposals survive a sibling’s validation error. A malformed or truncated response is rejected as a whole. The next round receives the errors. Transport/configuration
failures and solver unknown results terminate the run.

### Results

For `-d 20`, success means UNSAT at **every depth 0–19**. Each transition prefix
is checked separately. This establishes bounded safety, not an inductive proof.
A remaining SAT query means the batch did not close that bound; it does not
certify a real program counterexample.

Logs and `agent.result.json` go under `.yardbird/runs/<run>/`.
The result records closed/unresolved depths, cumulative instance counts, usage,
timings and the stop reason. Previously closed bounds are skipped; each round
checks the remaining bounds in a fresh solver session with the accumulated batch.
`unique_instances` counts retained schemas (or exact formulas in exact mode).
`installed_instances` counts distinct ground installations; `replayed_assertions` counts
reinstallation work across rounds. `usage_unknown_calls` flags calls whose token
usage was not returned, so recorded token totals may be incomplete.
Compare `total_seconds`, including inference and validation, with native runtime.
`--json-output` also writes the result to stdout. Incomplete, unknown, timeout and
error results return a nonzero exit status.

### Replay baseline (no LLM)

Record a successful native run, then check its exact instances without discovery:

```sh
./target/release/yardbird \
  -f examples/distributed_protocols/german/german.encoding.vmt \
  --policy german-fast -d 20 --wall-timeout-secs 500 \
  --export-instantiations german-native-instances.json --json-output

./target/release/yardbird \
  -f examples/distributed_protocols/german/german.encoding.vmt \
  --policy german-fast -d 20 --wall-timeout-secs 500 \
  --replay-instantiations german-native-instances.json --json-output
```

Export requires a fresh path and completion of all bounds. Replay requires the
same source and depth, validates every formula against the trusted schemas, and
preserves exact frame placements by default. Add `--one-shot-placement schema`
to normalize the recorded instances and measure native temporal replay instead.
Replay time excludes the original discovery
run. Replay artifacts are never supplied to the LLM.

### Offline tests

```sh
cargo test --lib agent_interaction::one_shot::tests
cargo test --test one_shot_tests
```
