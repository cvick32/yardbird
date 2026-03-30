# Bitwuzla Quantifier Support Plan

## Goal

Build a small analysis tool for SMT-LIB benchmarks that answers two questions:

1. Can this file be converted so that all quantification is represented using universal quantifiers only, after pushing negations to negation normal form (NNF)?
2. If not, why not?

This supports a benchmark split where:

- fully supported files are candidates for a future "strip quantifiers and re-add them as egg rewrites" pipeline
- unsupported files still remain in the benchmark suite, but will rely on the SMT solver's native quantifier instantiation

This document is for planning only. It does not propose implementation yet.

## Benchmark Scope

We want to import as many Bitwuzla array benchmarks as possible into:

- [examples/bitwuzla](/Users/cvick-admin/Documents/research/yardbird/examples/bitwuzla)

and preserve the source grouping so we can compare results by theory family and benchmark origin.

### Include

Include top-level SMT-LIB theory families whose logic actually contains arrays:

- `ABV`
- `ABVFP`
- `ABVFPLRA`
- `AUFBV`
- `AUFBVFP`
- `QF_ABV`
- `QF_ABVFP`
- `QF_ABVFPLRA`
- `QF_AUFBV`
- `QF_AUFBVFP`

from both:

- `benchmarks/incremental`
- `benchmarks/non-incremental`

### Exclude

Do not use a raw "directory name contains `A`" rule during import, because that over-selects non-array families such as:

- `FPLRA`
- `BVFPLRA`
- `QF_FPLRA`
- `QF_BVFPLRA`

Those contain the letter `A` as part of arithmetic, not arrays.

## Proposed Imported Layout

Mirror the Bitwuzla source structure under `examples/bitwuzla`:

```text
examples/bitwuzla/
  incremental/
    QF_ABV/
    QF_ABVFP/
    QF_ABVFPLRA/
    QF_AUFBV/
  non-incremental/
    ABV/
    ABVFP/
    ABVFPLRA/
    AUFBV/
    AUFBVFP/
    QF_ABV/
    QF_ABVFP/
    QF_ABVFPLRA/
    QF_AUFBV/
    QF_AUFBVFP/
```

Under each logic family, preserve the remaining source subdirectories as-is.

Example:

```text
examples/bitwuzla/non-incremental/AUFBV/20210301-Alive2/gcc/215_gcc.smt2
```

This keeps:

- theory family
- incremental vs non-incremental split
- original benchmark origin

## Current Findings

These numbers are from a quick survey of the source benchmark tree:

- `non-incremental/AUFBV`: `1522` files, all sampled quantifier-bearing files appeared `forall`-only
- `non-incremental/ABV`: `169` files total, about `100` with `forall`, `96` with `exists`, and at least `27` with both
- `QF_ABV`, `QF_AUFBV`, and the sampled incremental `QF_*` array families appeared quantifier-free in practice

This suggests:

- `AUFBV` is likely the best first target for the future universal-rewrite pipeline
- `ABV` contains genuine unsupported patterns, especially alternation
- `QF_*` families should still be included in the imported corpus even though quantifier conversion is trivial or irrelevant there

## Classification Rule

A file is **fully supported** if, after converting every asserted term to NNF, no existential quantifier remains anywhere in the formula.

Equivalent operational rule:

- after pushing `not` inward, any remaining `exists` means the file is **not fully supported**

This matches the intended semantics:

- `not (exists ((x T)) P)` becomes `forall x. not P` and is potentially supported
- `exists ((x T)) P` in positive polarity remains existential and is unsupported
- quantifier alternation is unsupported if NNF still contains `exists`

## Planned Classification Categories

Each file should receive one top-level support status plus a more specific reason code.

### Support status

- `fully_supported`
- `not_fully_supported`

### Reason codes

For the first version, use per-file reasons like:

- `quantifier_free`
- `forall_only`
- `exists_eliminated_by_nnf`
- `unsupported_exists_positive_polarity`
- `unsupported_alternation`

Optional refinement if useful during implementation:

- `parse_error`
- `unsupported_non_nnf_boolean_context`

The reason codes should be stable enough that benchmark results can be grouped by them later.

## Classification Semantics

The analysis should work over the parsed AST, not raw text.

### Normalization steps

For each file:

1. Parse with `smt2parser`.
2. Focus on asserted formulas.
3. Eliminate `let` bindings before classification.
4. Push negations inward to NNF.
5. Walk the resulting AST and classify quantifiers by polarity and nesting.

We should also save transformed versions of the files once parsing is done, so we have:

- the imported original benchmark
- a let-eliminated rendering
- an NNF rendering

That lets us inspect the expanded formulas later without rerunning the whole pipeline.

### Why AST-based analysis

The repository already has the pieces needed for a robust analysis pass:

- quantifiers are preserved in the AST by [smt2parser/src/concrete.rs](/Users/cvick-admin/Documents/research/yardbird/smt2parser/src/concrete.rs)
- visitor/rewriter infrastructure already exists in [smt2parser/src/rewriter.rs](/Users/cvick-admin/Documents/research/yardbird/smt2parser/src/rewriter.rs)
- let elimination already exists in [smt2parser/src/let_extract.rs](/Users/cvick-admin/Documents/research/yardbird/smt2parser/src/let_extract.rs)
- command streaming already exists in [smt2parser/src/lib.rs](/Users/cvick-admin/Documents/research/yardbird/smt2parser/src/lib.rs)

This avoids brittle regex classification and gives us exact reasons.

## Quantifier Handling Rules

The first implementation should use these rules.

### Supported

- formulas with no quantifiers
- formulas with only universal quantifiers
- formulas where an existential appears only under odd negation and becomes universal in NNF

Example:

```text
(not (exists ((x T) (y T)) P))
```

becomes:

```text
(forall ((x T) (y T)) (not P))
```

### Unsupported

- any existential that survives in NNF
- any alternation pattern that leaves an existential in NNF
- any formula where polarity analysis is ambiguous because NNF conversion is incomplete

Examples:

```text
(exists ((x T)) P)
(forall ((x T)) (exists ((y T)) P))
(not (forall ((x T)) (exists ((y T)) P)))
```

After NNF, each of those still contains an existential.

## Handling Incremental Benchmarks

The imported benchmark set should include both incremental and non-incremental families.

For the classifier, we should keep the first version deliberately simple:

- classify asserted formulas present in the file
- record whether the file uses incremental commands such as `push`, `pop`, or multiple `check-sat`

We will do whole-file classification in the first version.

That means:

- transform and classify all `assert` commands in parse order
- record incremental features like `push`, `pop`, and `check-sat-assuming`
- aggregate to one conservative file-level result

## Proposed Tool Output

The script should emit machine-readable results so future benchmark runners can join on them.

### Per-file output fields

- `path`
- `relative_path`
- `family`
- `incrementality`
- `has_arrays`
- `has_quantifiers`
- `has_forall`
- `has_exists`
- `fully_supported`
- `reason`
- `n_asserts`
- `n_forall`
- `n_exists`
- `n_exists_after_nnf`
- `uses_push_pop`
- `uses_check_sat_assuming`

### Aggregate output

The script should also be able to produce summary counts grouped by:

- `family`
- `incrementality`
- `fully_supported`
- `reason`

## Suggested Deliverables

Implementation should eventually produce:

1. A benchmark import script that copies the selected Bitwuzla families into `examples/bitwuzla`.
2. A quantifier support classifier for SMT-LIB files.
3. A manifest file for imported benchmarks and classification results.
4. A short README or usage note describing how to rerun the import and analysis.

## Proposed Phases

### Phase 1: Benchmark import

- copy selected array families into `examples/bitwuzla`
- preserve directory structure
- generate a manifest of copied files

### Phase 2: Formula classifier

- parse commands
- remove lets
- convert asserted formulas to NNF
- classify support status and reasons

### Phase 3: Reporting

- emit per-file JSON or CSV
- emit grouped summary counts
- make results easy to join with future benchmark outcomes

## Implementation Plan

This section turns the planning above into a concrete repo-specific implementation plan.

### Code placement

Use a split design:

- reusable parsing and quantifier-analysis logic in `smt2parser`
- a thin Yardbird CLI binary that drives import and classification

This keeps the AST work close to the parser while still making the workflow feel like a Yardbird benchmark tool.

### Proposed new files

In `smt2parser`:

- `smt2parser/src/analysis/mod.rs`
- `smt2parser/src/analysis/nnf.rs`
- `smt2parser/src/analysis/quantifier_support.rs`
- `smt2parser/src/analysis/import_manifest.rs`

In the root crate:

- `src/bin/bitwuzla_quantifier_support.rs`

### Why not extend `smt2bin`

[smt2parser/src/main.rs](/Users/cvick-admin/Documents/research/yardbird/smt2parser/src/main.rs) is still a generic parser demo built on `structopt`. This workflow is more naturally a Yardbird benchmark tool, and the root crate already uses `clap`.

The parser logic should still be implemented in the `smt2parser` library so the binary is only orchestration.

### Public library surface

Add a small reusable API to `smt2parser`.

#### Parsing helper

Update the existing command collection helpers in [smt2parser/src/lib.rs](/Users/cvick-admin/Documents/research/yardbird/smt2parser/src/lib.rs) so they are non-panicking and usable by the new workflow.

Reason:

- `get_commands` currently falls back to `todo!` on parse errors
- CV: let's just update the get_commands method to be non-panicking, it will be good anyway to spruce up this library. Also, we have full control of this, so it's fine
- the classifier needs to emit `parse_error` rows instead of crashing

Planned direction:

- change `get_commands` to return `Result<Vec<Command>, concrete::Error>`
- add a convenience wrapper that opens a file path and calls it

#### File analysis helper

Expose one top-level analysis entry point:

```rust
pub fn analyze_file(commands: &[Command], relative_path: &Path) -> AnalysisResult
```

That result should include:

- transformed commands for let-eliminated output
- transformed commands for NNF output
- per-assertion metadata
- whole-file metadata

### Core structs

Use serializable structs so the CLI can write JSON directly.

#### FileAnalysis

```rust
pub struct FileAnalysis {
    pub relative_path: PathBuf,
    pub family: String,
    pub incrementality: String,
    pub has_arrays: bool,
    pub has_quantifiers: bool,
    pub has_forall: bool,
    pub has_exists: bool,
    pub fully_supported: bool,
    pub reason: String,
    pub n_asserts: usize,
    pub n_forall: usize,
    pub n_exists: usize,
    pub n_exists_after_nnf: usize,
    pub uses_push_pop: bool,
    pub uses_check_sat_assuming: bool,
    pub parse_error: Option<String>,
}
```

#### AssertionAnalysis

```rust
pub struct AssertionAnalysis {
    pub index: usize,
    pub original: String,
    pub let_eliminated: String,
    pub nnf: String,
    pub n_forall_before: usize,
    pub n_exists_before: usize,
    pub n_exists_after_nnf: usize,
    pub reason: String,
}
```

#### ImportedBenchmark

```rust
pub struct ImportedBenchmark {
    pub source_path: PathBuf,
    pub relative_path: PathBuf,
    pub destination_path: PathBuf,
    pub family: String,
    pub incrementality: String,
}
```

### Import step

The import step should use an explicit family allowlist, not a pattern like "directory contains `A`".

#### Source roots

- `~/Documents/research/cav2023-bitwuzla-artifact/benchmarks/benchmarks/incremental`
- `~/Documents/research/cav2023-bitwuzla-artifact/benchmarks/benchmarks/non-incremental`

#### Family allowlist

- `ABV`
- `ABVFP`
- `ABVFPLRA`
- `AUFBV`
- `AUFBVFP`
- `QF_ABV`
- `QF_ABVFP`
- `QF_ABVFPLRA`
- `QF_AUFBV`
- `QF_AUFBVFP`

#### Destination root

- [examples/bitwuzla](/Users/cvick-admin/Documents/research/yardbird/examples/bitwuzla)

#### Import algorithm

1. Walk the two Bitwuzla source roots.
2. Keep only files whose first theory-family segment is in the allowlist.
3. Copy files into `examples/bitwuzla/<incrementality>/<family>/...`.
4. Preserve the remainder of the subtree exactly.
5. Write `import_manifest.json`.

### Saved transformed artifacts

Keep originals and derived outputs separate.

#### Originals

- `examples/bitwuzla/...`

#### Derived outputs

Write these under:

- `benchmark_results/bitwuzla_quantifier_support/`

with subdirectories:

- `let_eliminated/<relative-path>`
- `nnf/<relative-path>`
- `assertions/<relative-path>.json`

The transformed files should remain whole SMT2 files:

- non-assert commands preserved
- assert commands rewritten
- files re-rendered via `Command::to_string()`

This is better than storing only isolated transformed terms because we can inspect the full benchmark shape later.

### Transformation pipeline

For each file:

1. parse commands once
2. collect whole-file command metadata
3. rewrite every `assert` term with let elimination
4. rewrite every let-eliminated `assert` term to NNF
5. classify each assertion
6. aggregate assertion results to one whole-file result
7. write transformed files plus JSON metadata

### Let elimination plan

Reuse [smt2parser/src/let_extract.rs](/Users/cvick-admin/Documents/research/yardbird/smt2parser/src/let_extract.rs) directly.

Behavior:

- transform only `assert` terms
- preserve non-assert commands unchanged
- store the let-eliminated string form in `AssertionAnalysis`

### NNF conversion plan

Implement a dedicated recursive transformer in `smt2parser/src/analysis/nnf.rs`.

#### Core API

```rust
fn to_nnf(term: Term, polarity: Polarity) -> Result<Term, NnfError>
```

We checked for an existing NNF pass and did not find one in `smt2parser`, so the current plan is a small hand-rolled polarity-based transformer.

with:

- `Polarity::Positive`
- `Polarity::Negative`

#### Required rewrites in v1

- `not`
- `and`
- `or`
- `=>`
- `forall`
- `exists`
- `attributes`

The key quantifier rewrites are:

- negative `forall` becomes positive `exists`
- negative `exists` becomes positive `forall`

The key boolean rewrites are:

- negative `and` becomes positive `or`
- negative `or` becomes positive `and`
- implication is desugared before pushing polarity into children

#### Conservative fallback

If a quantifier appears inside a boolean context we do not normalize confidently in v1, return a structured error and classify conservatively.

Examples to treat carefully:

- boolean-valued `=`
- `xor`
- `ite` with quantified branches

That is why `unsupported_non_nnf_boolean_context` is a useful optional reason code.

### Classification plan

Run classification on the NNF form, not the original term.

#### Assertion-level classification

For each assertion:

- `quantifier_free` if no quantifiers occur
- `forall_only` if quantifiers occur and no existentials remain after NNF, and there were no existentials before NNF
- `exists_eliminated_by_nnf` if existentials occurred originally but all disappeared after NNF
- `unsupported_alternation` if existential quantifiers still remain after NNF in a nested mixed pattern
- `unsupported_exists_positive_polarity` if existential quantifiers still remain after NNF without needing the more specific alternation label
- `parse_error` for parse failures
- `unsupported_non_nnf_boolean_context` if normalization bails out conservatively

#### Whole-file aggregation

The file is `fully_supported = true` only if every assertion is fully supported.

Use a fixed severity order when collapsing assertion reasons to a file reason:

1. `parse_error`
2. `unsupported_non_nnf_boolean_context`
3. `unsupported_alternation`
4. `unsupported_exists_positive_polarity`
5. `exists_eliminated_by_nnf`
6. `forall_only`
7. `quantifier_free`

### Incremental benchmark handling

Use whole-file classification in v1.

Implementation details:

- count `push` and `pop`
- count `check-sat` and `check-sat-assuming`
- transform and classify all `assert` commands in parse order
- do not reconstruct assertion-stack snapshots yet

This keeps the first version simple while still recording enough metadata to revisit incremental semantics later.

### CLI plan

Implement a dedicated workspace binary:

- `cargo run --bin bitwuzla_quantifier_support -- ...`

#### Proposed subcommands

```text
bitwuzla_quantifier_support import
bitwuzla_quantifier_support classify
bitwuzla_quantifier_support import-and-classify
```

#### `import`

Inputs:

- source benchmark root
- destination root
- optional family allowlist override

Outputs:

- copied benchmarks
- `import_manifest.json`

#### `classify`

Inputs:

- benchmark root, usually `examples/bitwuzla`
- output root, usually `benchmark_results/bitwuzla_quantifier_support`

Outputs:

- `file_analysis.jsonl`
- `summary.json`
- whole-file transformed outputs
- assertion-level JSON

#### `import-and-classify`

Convenience wrapper for full regeneration.

### Output format

Use:

- JSONL for per-file rows
- pretty JSON for manifests and grouped summaries

Reason:

- JSONL is easy to stream and post-process
- pretty JSON is easy to inspect manually

### Test plan

#### Unit tests in `smt2parser`

Add focused tests for:

- let elimination preserving quantifiers
- `not (exists ...)` becoming `forall ...` in NNF
- nested `forall/exists` alternation remaining unsupported
- attributes wrapping quantified terms
- whole-file aggregation logic
- conservative failure on unsupported boolean contexts

CV: we also want to make sure we have a lot of good test cases for this flow

Use helpers already available in [smt2parser/src/lib.rs](/Users/cvick-admin/Documents/research/yardbird/smt2parser/src/lib.rs):

- `get_term_from_term_string`
- `get_command_from_command_string`

#### Small fixture tests

Create tiny SMT2 fixtures for:

- quantifier-free file
- forall-only file
- exists-eliminated-by-nnf file
- unsupported alternation file
- incremental file with `push/pop`

#### Import tests

Prefer unit tests for import mapping:

- allowlist inclusion and exclusion
- source path to destination path mapping

### Performance plan

To keep v1 reasonable on large `AUFBV` files:

- parse each file once
- avoid solver calls entirely
- avoid semantic simplification beyond let elimination and NNF
- stream per-file JSON rows as files are processed
- write transformed files immediately instead of keeping everything in memory

### Non-goals for v1

Do not do these yet:

- generate egg rewrites
- prove semantic equivalence beyond syntactic NNF conversion
- reconstruct assertion-stack snapshots for incremental benchmarks
- integrate classification directly into `garden`

Those can come once we trust the imported corpus and labels.

## Risks and Edge Cases

### 1. Top-level family name ambiguity

Selecting families by the presence of the character `A` is not reliable. Import should use an explicit allowlist of array logics.

### 2. Incremental semantics

A benchmark may contain multiple assertion-stack states. A whole-file
classifier may be conservative, which is acceptable for the first pass
if we record incremental features.

### 3. Formula size

Some `AUFBV` files are large and contain very large quantifier
prefixes. The classifier should avoid expensive transformations beyond
let elimination and NNF.

### 4. Attributes and annotations

SMT-LIB attributes should be preserved or ignored safely during
classification, not dropped unsafely.

### 5. Future rewrite extraction

This plan only classifies support. It does not yet specify:

- how universal formulas become egg rewrites
- how side conditions are represented
- how quantified formulas over rich boolean structure are compiled into rewrites
- CV: that's fine, though we should be thnking about how we want to handle these cases
Those should be planned separately once we know the benchmark distribution.

## Recommended First Experimental Target

Start future implementation and benchmarking with:

- `non-incremental/AUFBV`

Reason:

- large corpus
- quantifier-bearing
- appears overwhelmingly `forall`-only
- should give the cleanest signal for the universal-rewrite idea
- CV: sounds good
Then expand to:

- `ABV` as a stress-test bucket for unsupported patterns
- `QF_*` families as control groups

## Questions Resolved

The following decisions are now fixed for this plan:

- include as many array families as possible, including `QF_*` variants
- a file is fully supported only if every quantifier can be converted to universal form in NNF
- after NNF, any remaining existential means unsupported
- keep unsupported benchmarks in the imported corpus and classify them with reason codes for later result slicing

For most parser/compiler-style code, NNF is simple enough to implement directly. It is basically two passes, or even one recursive pass:
Eliminate high-level Boolean connectives:
=>
xor
=, if used as Boolean equivalence
maybe ite if your NNF definition disallows it
Push negations inward using De Morgan until not only appears on atoms.
Typical rules:
not (and a b) → or (not a) (not b)
not (or a b) → and (not a) (not b)
not (not a) → a
not (=> a b) → and a (not b)
a => b → or (not a) b
a = b for Boolean terms → (or (and a b) (and (not a) (not b)))
What matters in SMT2 is your definition of atom. Usually, atoms are things like:
predicates: (< x y), (= x y) over non-Bool terms
Boolean variables/constants
theory atoms in general
Then NNF means not is only allowed directly above those atoms.
So for example:
not (= x y) is fine in NNF if x and y are Ints
but if a and b are Bool, then not (= a b) is usually expanded further because Boolean equality is really equivalence
That distinction is the main place people get NNF wrong in SMT-style parsers.
My recommendation:
Do not use Z3 just for NNF conversion unless your whole pipeline is already solver-centric. It adds:
dependency on solver ASTs
less control over output form
possible surprises from simplification/reformatting
A hand-rolled NNF pass is:
small
deterministic
easy to test
A good implementation shape is:
to_nnf(expr) calls nnf(expr, polarity=true)
nnf(e, polarity) means “convert e assuming it appears under an even or odd number of negations”
This polarity-based style is cleaner than building explicit Not nodes and then re-traversing them.

CV: we also want to make sure we have a lot of good test cases for this flow
