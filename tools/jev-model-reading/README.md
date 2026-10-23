# Jev model-reading experiment

Probe whether Jev can evaluate a captured countermodel before asking it to search
for instantiations. Python 3.10+ and the `z3` executable are required; no Python
packages are needed. Commands below run from the repository root.

`depth3.json` contains the **unchanged native model string and declarations** from
`yardbird-jev-copy-batch.jsonl`, model version 11, depth 3, query 140. It is the
last countermodel before ordinary refinement resolved this array-copy run. The
fixture records the source log's SHA-256 and does not depend on that untracked
log being present. It contains no API key, prior responses, or feedback.

## Latest completed diagnostic: native versus grouped model tables

The previous prompt, worked-example, alias, and presentation variants are retired
from active evaluation: their isolated gains did not establish an improvement on
the target nested reasoning task. Historical logs and replay options below remain
available as experimental evidence. The current baseline is the production
property-directed prompt, complete original VMT, and full native model, without
additional examples or alternate representations.

```bash
python3 tools/jev-model-reading/intermediates.py --live \
  --suite grouped --modes independent --examples none \
  --task-context property-directed --views native grouped --max-queries 144 \
  --output ./jev-reading-grouped.jsonl
```

The grouped condition **replaces** `state.model` with a complete grouped
interpretation. It does not append a second copy of the native dump. Every named
constant (including Booleans), explicit function entry, and default is preserved;
declarations and original VMT remain unchanged. Each function has `argument_order`,
one top-level `default`, and `entries` nested by successive argument values. For
Write this means array → index → written value → result. A missing key at any
level uses the function's default. The serializer neither evaluates terms nor
selects groups based on the question. Tests reconstruct every original tuple.

The 24 questions combine the ten lookup probes with the original 14-question
suite, including nested reads, balanced true/false formula controls, and binding
choice. Two views and three paired shuffles produce 144 calls. All questions are
independent: no mechanical substitution, earlier answers, worked examples, or
domain-value renaming. This tests both isolated lookup and the original task;
it is not yet a production model-format change.

The 2026-10-22 run scored 44/72 for native and 43/72 for grouped. Grouping improved
the fully resolved default Write lookup (0/3 to 3/3) but broke explicit Write
controls (6/6 to 0/6). Nested Read remained 0/3 in both conditions, and binding
choice remained 1/3. Grouped tables are therefore retained for reproduction, not
promoted over the native production baseline. These are repeated probes of one
countermodel, not independent benchmark instances.

## Completed diagnostic: mechanical substitution

Mechanical substitution is retained for reproduction, not active promotion. It
improved intermediate answers without fixing the critical Write lookup or improving
final classification on the two tested formulas, at 9–11 calls per formula.

```bash
python3 tools/jev-model-reading/intermediates.py --live \
  --suite substitution --modes independent substituted --examples none \
  --task-context property-directed --views native --max-queries 120 \
  --output ./jev-reading-substitution.jsonl
```

The baseline asks each expression independently. The substituted condition first
asks Jev for leaf-symbol values, then replaces previously answered subexpressions
with **Jev's selected values**, including incorrect ones. Rewriting matches exact
AST subtrees, never evaluates them, never rewrites literals/function names, and
does not recursively rewrite inserted answers. No solver correction, earlier
correctness labels, original nested expression, or working notes are sent with
the rewritten question. The full interpretation and prompt remain unchanged.

Both conditions share offered options and shuffles. All integer values occurring
in the interpretation are offered for integer questions, and all array-domain
values for array questions. The source-read chain uses 11 calls; the constant-one
control uses 9. With three trials and two conditions this makes 120 calls. Asking
the original complete formula directly costs one call; the other independent
questions are diagnostic controls, not a baseline runtime requirement.

Results distinguish correctness for the original expression (`correct`) from
correctness for the rewritten question (`local_correct`). A locally correct
answer can propagate an earlier mistake. `chain_summary` reports final accuracy,
all-steps-correct chains, calls, and summed client time per chain. Solver-derived
scores stay outside wire payloads. Dry runs do not invent Jev answers, so their
substituted questions remain unreduced. This is a diagnostic prototype, not a
change to Yardbird's production policy.

## Inspect requests without inference

```bash
python3 tools/jev-model-reading/run.py run \
  --presentation native relevant tables \
  --shuffle-options --seed 0 \
  --output /tmp/jev-reading-preview.jsonl
```

This creates 42 planned requests: 14 questions × 3 presentations. It runs the
local Z3 answer check, but **makes no network requests and needs no API key**.
Output files must be new. To inspect the actual wire payload, read a `request`
record's nested `request` object. Sibling fields such as `expected_choices` and
`oracle_values` are private scoring metadata and are never sent to Jev.

## Run the experiment

Start with the six balanced true/false classification questions on the full
native model:

```bash
python3 tools/jev-model-reading/run.py run --live \
  --question classify-1 classify-2 classify-3 classify-4 classify-5 classify-6 \
  --presentation native --shuffle-options --seed 0 \
  --output ./jev-reading-classification.jsonl
```

Or compare the entire suite across presentations:

```bash
python3 tools/jev-model-reading/run.py run --live \
  --presentation native relevant tables \
  --shuffle-options --seed 0 \
  --output ./jev-reading-comparison.jsonl
```

The key comes from `JEV_API_KEY` in the environment, or the repository's `.env`.
`--env-file` changes that path. The small `.env` reader accepts plain or quoted
assignments and optional `export`; it does not execute shell expressions or
expand variables. The client reuses an HTTPS connection. HTTP/transport errors
are logged and stop the run; there are no automatic retries or duplicate paid
queries. A failed request's cost is unknown unless usage was returned.

## Questions and controls

| Category | Questions | Capability |
|---|---:|---|
| `lookup` | 2 | Symbol resolution and explicit function-table lookup |
| `default` | 1 | Applying an `else` value |
| `composition` | 2 | Nested Read/Write evaluation, including defaults |
| `logic` | 1 | Evaluating an unequal-index condition |
| `classification` | 6 | Three true and three false complete formulas, including a false-antecedent control |
| `comparison` | 1 | Selecting the violated axiom from three complete instances |
| `binding` | 1 | Selecting `val` with array, write index, and read index fixed |

Each question is a fresh, independent request. No previous answer, intermediate
evaluation, or corrective feedback is included. Question/presentation order is
randomized reproducibly by `--seed`. With `--shuffle-options`, option labels are
also shuffled; the same question/trial uses the same shuffle across presentations
to make comparisons paired.

The binding question intentionally accepts **all** options that make the formula
false. In this model both `0` and `(Read_Int_Int a@0 i@0)` work for the fixed
bindings. Choosing the latter is not required to pass. Reported
`correct_probability` is the sum of probability assigned to acceptable options;
`chance_accuracy` reflects the number of acceptable options. Most other
questions have one correct option. This is a model-reading diagnostic, not a
measurement of whether an instance advances the entire proof.

## Presentations

- `native`: Exact native Z3 model string from the capture (the default).
- `relevant`: Native syntax, retaining constants and table entries traversed
  when evaluating **all** options/expressions in that question. Defaults remain
  present. This uses the oracle to isolate relevant information deliberately; it
  is an assisted diagnostic condition, not an equivalent end-to-end search
  policy. Omitted entries need not preserve evaluations of unrelated terms.
- `tables`: The full interpretation as JSON constants, explicit argument/value
  entries, and defaults. It preserves the same values and includes no computed
  answers or evaluation traces.

All presentations retain the captured declarations. `--anonymize` consistently
renames modeled constants and function names in the interpretation, declarations,
questions, and answer options. It leaves sorts and model-domain values intact.
Use a separate output file for a paired run with this flag; the native string is
otherwise preserved exactly. `--repeats N` measures sensitivity to repeated calls
and, with shuffling, option order. It does not create independent benchmarks.

Other controls: `--model`, `--timeout`, `--max-queries` (default 100), `--z3`,
`--input-usd-per-million` (default 0.042), and `--output-usd-per-million` (default
0). Prices are configurable estimates, not a fetched tariff or bill. No inference
calls occur unless `--live` is provided. The full 42-question experiment repeated
three times needs `--max-queries 126`.

### Explain the verification use case

`--task-context refinement` prepends an explanation of Yardbird's abstraction
refinement task: arrays have been replaced with uninterpreted functions, the
candidate countermodel may violate array theory, and a false complete axiom
instance is needed to exclude it. It also explicitly preserves true control
questions. This changes only `state.task`; no evaluations, term preferences,
shortlists, or answers are added. The default `baseline` retains the original
prompt for comparison. Keep the seed and other flags fixed between runs:

```bash
python3 tools/jev-model-reading/run.py run --live \
  --task-context refinement \
  --presentation native relevant tables --shuffle-options --seed 0 \
  --output ./jev-reading-refinement-context.jsonl
```

`--task-context falsification` instead replaces `state.task` with the user's
five-paragraph prompt stored verbatim in `FALSIFICATION_PROMPT`. It emphasizes
evaluating complete instances, avoiding simplification by the axiom under test,
and choosing partial bindings that admit a false completion. The question-specific
instructions, options, and model remain unchanged; the baseline task text and
the earlier refinement context are not appended to this variant.

### Include the original problem

`--vmt examples/array/array_copy.vmt` adds the complete UTF-8 source verbatim in
`state.problem.source`, together with a short mapping from VMT labels, select/store,
and next-state variables to the abstract model notation. It does not change the
model, prompt, questions, or options, and performs no dataflow analysis or source
selection. The log records the source hash and byte count. This cannot be combined
with `--anonymize`, which would disconnect source names from model names.

```bash
python3 tools/jev-model-reading/run.py run --live \
  --task-context falsification --presentation native \
  --vmt examples/array/array_copy.vmt --shuffle-options --seed 0 \
  --output ./jev-reading-full-vmt.jsonl
```

This sends 14 requests. The summary includes maximum serialized request bytes
and reported input-token totals/range. Byte counts are not token-limit estimates;
the service's reported usage is the token measurement. Inputs are never silently
truncated. An API input-limit rejection is recorded and stops the experiment.

### Property-directed selection experiment

`--task-context property-directed --vmt examples/array/array_copy.vmt` uses the
standalone prompt in `src/policy/decision_model/prompts/property-directed.txt`.
It explicitly prefers terms affecting the property violation and appearing in
the transition system, while retaining the requirement that the complete instance
be false. This is an intentional relevance preference; no terms are removed or
ranked by host-side dataflow analysis. The new prompt includes a reminder to
answer true diagnostic controls truthfully, so it is a distinct prompt rather
than a one-sentence ablation of `falsification`.

The same prompt can be used in Yardbird's actual refinement loop. Jev policies
now include the complete original VMT in every query, including conditional
binding steps. Their substitution catalogues omit Boolean terms (no supported
array axiom slot accepts them), but retain all integer/array descendants of
Boolean formulas. The full native model, including Boolean interpretations,
declarations, original VMT, and installed-instance context remain intact.
`--jev-prompt baseline` retains the previous task wording;
`--jev-prompt property-directed` selects this new prompt:

```bash
./target/quick/yardbird -f examples/array/array_copy.vmt -d 30 \
  --policy conditional-binding --jev-prompt property-directed \
  --jev-batch --jev-candidates 10 --jev-beam-width 3 \
  --jev-attempts 5 --jev-timeout-secs 2 --wall-timeout-secs 120 \
  --jev-log ./yardbird-jev-copy-property-directed.jsonl \
  --json-output > ./yardbird-jev-copy-property-directed.json
```

Ordinary refinement still runs after an unsuccessful Jev episode. Inspect the
run profile's `PolicyCandidates` and ordinary operation records to distinguish
their contributions. Completing depth 29 is a bounded check, not an inductive
proof of the property for all executions.

## Paired prompt/context ablations

Run all four variants on identical questions, the full native model, and the
complete original VMT:

```bash
python3 tools/jev-model-reading/run.py run --live \
  --ablation property-directed procedural procedural-examples procedural-aliases \
  --vmt examples/array/array_copy.vmt --repeats 3 \
  --shuffle-options --seed 0 --max-queries 168 \
  --output ./jev-reading-ablations.jsonl
```

Omit `--live` for an offline preview. This sends 14 questions × 4 variants × 3
trials. Jobs are interleaved in seeded random order, and option shuffles and
answer keys are paired across variants for each question/trial. No previous
answers or feedback are sent. `summarize` separates variants in its breakdown.

- `property-directed`: the current production prompt, including the source-read
  preference, as a control.
- `procedural`: a standalone table-evaluation algorithm emphasizing complete
  tuple matching, defaults, nested applications, and implication semantics.
- `procedural-examples`: the procedural prompt plus two fixed, unrelated toy
  interpretations with worked true and false examples. These teach evaluation
  mechanics without supplying answers from the captured countermodel.
- `procedural-aliases`: the procedural prompt plus a complete inverse index of
  modeled named constants, grouped by value. The native model stays byte-for-byte
  intact. This index does not evaluate compound terms, select relevant symbols,
  or remove function entries/defaults. Boolean and integer values remain distinct.

The examples and aliases variants each add just one context field to procedural.
Property-directed versus procedural compares whole prompts, not a single-sentence
ablation. These presets require native presentation, original symbols, and VMT;
they cannot be combined with a separate `--task-context` override. Procedural
is also available independently via `--task-context procedural`.

All violating answers remain acceptable in the binding probe. A preference for
source reads is not part of its correctness criterion. Three trials of this one
capture measure sensitivity, not generalization across programs or countermodels.

## Intermediate-answer experiment

```bash
python3 tools/jev-model-reading/intermediates.py --live \
  --output ./jev-reading-intermediates.jsonl
```

Omit `--live` for an offline preview. Defaults make 168 calls: two worked-example
conditions × two note modes × two expression chains × seven steps × three
paired option shuffles. Each request retains the full native model, declarations,
VMT source, and procedural prompt. This script reuses `run.py`'s client, oracle,
scorer, and configurable cost estimation; existing output files are rejected.

`--examples generic nested` compares the earlier generic F/G examples with an
unrelated toy Read/Write interpretation. The nested example works through both
a false source-read instance and a true constant-value instance. Its local symbols,
domain elements, and values are separate from the captured countermodel.

`--modes independent carried` compares fresh questions with questions containing
Jev's own earlier selected expression/value pairs. Carried answers are explicitly
unverified working notes and may be revised; they are not substituted as immutable
facts. No oracle values, correctness labels, or corrected intermediate results
are included in requests. Dry runs leave notes empty rather than fabricate answers.

The source-read and constant-one chains ask for the value argument, Write result,
outer Read, comparison Read, index guard, consequent equality, and complete axiom.
Write-result choices include every array-domain value occurring in the full
interpretation. These are evaluation answers, not production substitution terms.
Chains are interleaved randomly while preserving step order within each chain;
each chain starts with empty notes. Invalid answers or transport errors stop the
run without retries. Logs include all responses and private solver-checked answer
keys; stdout summarizes results and selected values by condition and step.

These are explicit subquestion answers, not access to Jev's internal reasoning.
Fresh outer-read and complete-axiom probes supply controls for any benefit of
carrying answers. This is still one captured countermodel, and the nested example
deliberately teaches a structure close to the tested task.

### Isolate Write lookup from composition

```bash
python3 tools/jev-model-reading/intermediates.py --live \
  --suite lookup --modes independent --max-queries 60 \
  --output ./jev-reading-lookup.jsonl
```

This runs ten independent questions with both example contexts and three paired
shuffles. It compares nested Write, source-value-inlined Write, array-resolved
Write, and fully resolved Write; includes explicit Write rows with values 1 and
0 as controls; and probes resolved Read default/explicit lookups plus exact row
matching with true/false controls. All array-domain values remain offered.

The inlined values are deliberate assisted diagnostic stimuli based on this
fixture, not a production context optimization. The evaluator and Z3 check every
question. A row-match question's first two arguments are identical, so its answer
key is the equality of the third arguments. Questions remain independent and the
full native model and VMT are unchanged.

### Lossless representation comparison

```bash
python3 tools/jev-model-reading/intermediates.py --live \
  --suite lookup --modes independent --examples generic \
  --views native native-short named named-short --max-queries 120 \
  --output ./jev-reading-representation.jsonl
```

This crosses two presentation choices while holding the procedural prompt and
generic worked examples fixed: native syntax versus JSON rows with named
`array`, `index`, and `value` fields, and original domain identifiers versus
short `array_N` identifiers. All constants, function entries, and defaults are
retained. Named tables include positional parameter order. Short naming replaces
domain tokens consistently in the model, questions, options, and carried notes;
it does not rename program variables or function symbols. Option IDs and scoring
stay paired. Logs record both displayed and original selected values.

The default three trials produce 120 calls for the ten lookup questions. Each
view is reported separately. Tests reconstruct every original entry/default and
reverse the identifier renaming to check that these transformations preserve the
interpretation and questions. No question-specific filtering or evaluation is
used to construct the views. `--views` also works with intermediate chains.

## Oracle and extensibility

The local evaluator handles this capture's flat Int/Bool/uninterpreted-domain
tables and the small expression language needed by the probes. It fails on
unsupported values, unknown symbols, or unsupported operations instead of using
model completion. It is not a general native-Z3-model parser.

Before sending requests, the runner translates the captured interpretation into
SMT-LIB function definitions, declares distinct model-domain elements, checks
consistency, and asks Z3 whether each expression can differ from the evaluator's
answer. Every such check must return `unsat`. The log records the Z3 version,
fixture hash, runner hash, configuration, and source provenance.

To experiment with another breakdown, extend `request_for()` with a presentation
and add it to the CLI choices. To change the questions, edit `suite()`; expected
answers come from the evaluator, not from the question text. `--fixture` accepts
another file with the same `model`, `declarations`, and `provenance` fields, but
these probes intentionally reference this program's names and frames. Questions
must be adapted if those names or their candidate answers no longer apply.

## Results

```bash
python3 tools/jev-model-reading/run.py summarize ./jev-reading-comparison.jsonl
```

The summary groups accuracy, outcome counts, and probability on acceptable
answers by presentation and question category, along with client elapsed time
and estimated cost. It distinguishes accuracy over answered requests from
accuracy over all sent requests. Missing probability tables do not invalidate a
legal choice, but produce a null probability score. Full responses, resolved
model names, and usage remain in the log. Interrupted requests have unknown cost;
an incomplete final JSONL line is tolerated. Dry runs have no accuracy results.

A single captured model gives diagnostic evidence, not a general capability
estimate. In particular, native-vs-relevant differences confound context length
with oracle-assisted relevance selection; they do not by themselves identify
why the full-context condition fails.

## Tests

```bash
python3 -m unittest discover -s tools/jev-model-reading -p 'test_*.py' -v
```

Tests exercise the captured failure and its controls, Z3 disagreement detection,
reduced-model equivalence on every probe, symbol renaming, answer isolation,
multiple valid answers, seeded shuffling, costs, interrupted logs, and the live
execution path with a fake client. They make no inference calls.
