# Quantifier provenance and profiling

This is the provenance checkpoint: it adds observation only. Candidate ordering,
search limits, winner selection and the timing of solver checks are unchanged.

Use `--profile --json-output` for VMT abstract runs. The JSON result's `profiling`
object contains `quantifier_provenance` once per run. Each refinement/cost record
can contain `quantifier_work`, keyed by rule name and then phase.

## Source and lowering identities

`quantifier_provenance.sources` is a dictionary keyed by run-local source IDs.
The IDs derive from the normalized VMT command index and structural expression
path, and are deterministic for the same parsed input. They are not stable across
arbitrary edits, and are not input-file byte or line locations.

Each source contains:

- `kind` and `formula`: the parsed binder before alpha-renaming, let expansion in
  the quantifier pipeline, or property Herbrandization. This is normalized SMT
  syntax, not a byte-for-byte excerpt of the file.
- `command_index`, `command`, and `expression_path`: the containing normalized
  command (`define-fun NAME` or `assert`) and binder location. Path entries index
  application arguments; an attribute/binder body is child 0; let values precede
  the let body. Commands are those returned by `VMTModel::as_commands()`.
- `parent_source_id`: the enclosing binder, if present.
- `variables`: original names/sorts paired with globally fresh scoped names.
- `property_witnesses`: scoped-variable/witness-constant pairs. They remain
  available when property rewriting generates no input-binder rule.
- `eliminated_as_constant_array`: records a binder-independent lambda lowered
  to constant arrays instead of a generated lambda rule.

`quantifier_provenance.rules` is keyed by the same `input-binder-...` names used
in search profiles. It records `source_id`, the helper name and lowered kind,
scoped-to-lowered variable mappings, captures, witness function names, and the
lowered body. Witness functions correspond to the bound variables in order.
Captured lowered variables can be resolved using the other generated rules'
variable mappings and their source dictionary entries; global symbols retain
original names. Source identity is preserved when let expansion generates more
than one rule from the same original binder.

Nested source formulas keep the original lexical variable names, even when those
names shadow one another. The scoped names make the generated mappings unambiguous.
Arrays' built-in axioms retain their existing rule identities; this catalog maps
input binders, including exists/forall/lambda, rather than inventing source
quantifiers for built-in axioms.

## Work measurements

`cost_records[].quantifier_work[rule][phase]` contains `counters` and
`timing_secs`, associated with that record's depth and refinement step. Search
phases use the existing `input_binder_witnesses`, `input_binder_triggered_conflicts`,
`input_binder_conflicts`, and `input_binder_expansion` labels. Actual solver
installation has a separate `installation` phase.

Counters distinguish returned matches (which may include searched prefixes),
examined matches, obligation cache hits/misses, evaluation-cache hits, actual
model evaluations, satisfied-or-unresolved matches, matches sent to grounding,
grounding attempts, grounded/selected candidates, and known-or-uninstallable
candidates. A non-false evaluation is not necessarily a proven-satisfied formula;
the counter name preserves that distinction.

Installation records count actual abstract instances added, indexed assertions
added and indexed assertions deduplicated. These are distinct from selected
candidates and from helper-definition assertions; one abstract instance can
produce several framed assertions. Source formulas are never repeated per event.

Per-rule times cover matching, model filtering, formula construction, model
evaluation, and grounding/instantiation. `model_filter` contains construction and
evaluation: do not add them. Model evaluation includes the backend's translation,
evaluation and result conversion, and is distinct from solver `check()` time.
Extractor initialization and whole-batch selection remain shared costs; the latter
is exposed as `input_binder_selection` in the record's ordinary `timing_secs`.
Do not attribute a shared batch timer to an individual binder.

## Investigator queries

The deterministic summary and `quantifiers` view join rules to original formulas.
For an existing investigator run directory:

```sh
uv run --project tools/benchmark_investigator investigator query RUN_DIRECTORY quantifiers
uv run --project tools/benchmark_investigator investigator query RUN_DIRECTORY quantifiers --depth 0 --rule SOURCE_ID
```

`--rule` accepts an input-binder rule name or a source ID in the quantifiers view.
The view retains parent formulas for context and supports refinement filtering.
Responses remain bounded. Older profiles without a provenance dictionary are
explicitly marked unavailable rather than reverse-engineering source identities
from generated names. Existing Rust JSON readers also accept profiles without
these newly added fields.

Completed profiling records and the source catalog survive Yardbird-managed
inconclusive/error results and cooperative timeouts. External process kills still
cannot provide final JSON; no mid-action checkpointing or early batch return is
part of this change. Recording is enabled by profiling; no provenance is used to
make search decisions.
