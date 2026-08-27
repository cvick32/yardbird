# Yardbird

This chicken lays `egg`s...

# Running with Debug logs

`RUST_LOG='yardbird=debug,smt2parser=debug' cargo run -- ...`


# Artifact Evaluation

## Quick Start

For a quick assessment of the artifact, follow these steps:

### 0. Login to the VM

An .ova of the Ubuntu 22.04 image with all dependencies installed is given in `yardbird-vm.ova`.

username: yardbird
password: yardbird

### 1. Build the Tool

If there are any problems with Z3 header files during the build, be sure to run `source ~/.bashrc` to
put the correct headers in the path.

```bash
cd yardbird

# Build yardbird, with Z3
cargo build -p yardbird --release

# Build yardbird, with Z3 and cvc5
cargo build --release --features cvc5-backend

# Verify build
./target/release/yardbird --help
```

### 2. Run a Single Example

This will automatically use the BMC Cost strategy.

```bash
# Run on a simple array copy example (completes in ~1 second)
./target/release/yardbird --filename examples/array/array_copy.vmt --depth 10
```

To collect profiling data for every solver check, add `--profile --json-output`:

```bash
./target/release/yardbird \
  --filename examples/array/array_copy.vmt \
  --strategy concrete \
  --profile \
  --json-output
```

The profile contains solver checks and driver timings for every strategy. For
abstract strategies it also contains detailed e-graph and cost-function records.
Each solver record includes run/check/refinement identity, benchmark and
strategy metadata, nanosecond phase timings, instance counts, and complete
solver-statistics before, after, and delta snapshots.

To preserve a complete solver run as a directly replayable incremental SMT-LIB
session, use `--solver-capture-dir`. Capture implies profiling:

```bash
./target/release/yardbird \
  --filename examples/array/array_copy.vmt \
  --depth 1 \
  --strategy concrete \
  --solver-capture-dir capture/array-copy
```

The directory contains `solver-session.smt2`, `solver-session.index.json`,
`yardbird-profile.json`, and `manifest.json`. The transcript records the
effective logic, options, seeds, declarations, assertions, property scope, and
every check command in solver-call order. The index correlates each check with
its BMC depth and refinement identity and records separate setup, check-command,
and post-check byte boundaries. It can be replayed directly:

```bash
z3 -smt2 capture/array-copy/solver-session.smt2
```

To build the matched Z3 pair and immediately replay the capture through both
executables, pipe the builder result into the replay command:

```bash
python3 tools/z3-builder/z3_builder.py \
  --z3-checkout /path/to/z3 \
  --instrumented-checkout /path/to/instrumented-z3 \
  --output /tmp/yardbird-z3-build |
  python3 tools/z3_array_probe.py replay \
    --capture-dir capture/array-copy
```

The builder writes progress to stderr and its machine-readable manifest to
stdout. Replay reads the stock and instrumented binary paths from that manifest,
uses one persistent process per binary, and requires both ordered result
sequences to match the capture. To rerun without rebuilding, pass the existing
builder output directory instead:

```bash
python3 tools/z3_array_probe.py replay \
  --capture-dir capture/array-copy \
  --z3-build-dir /tmp/yardbird-z3-build
```

Use `--timeout` to change the default 60-second limit for each full replay.

To measure stock Z3 repeatedly without changing the correctness replay command,
use the separate `time` operation:

```bash
python3 tools/z3_array_probe.py time \
  --capture-dir capture/array-copy \
  --z3-build-dir /tmp/yardbird-z3-build \
  --warmups 3 \
  --repetitions 15
```

This retains every measured check sample, reports median and median absolute
deviation, and groups checks by BMC depth. Depth samples are summed within each
repetition before aggregation. The default machine-readable report is
`capture/array-copy/stock-timing.json`.

Once the instrumented Z3 build emits array-envelope summaries, join both timing
boundaries with the Yardbird check metadata using `compare`:

```bash
python3 tools/z3_array_probe.py compare \
  --capture-dir capture/array-copy \
  --z3-build-dir /tmp/yardbird-z3-build \
  --warmups 3 \
  --repetitions 15
```

The comparison fails if either solver's ordered SAT/UNSAT results differ from
the capture. Its `stock_external` and `instrumented_external` fields are
equivalent pipe round trips and expose instrumentation overhead. The
`instrumented_internal`, `array_envelope`, and `non_array_residual` fields come
from the same internal Z3 check boundary, so only those fields are subtracted
from one another. Measured stock and instrumented repetitions are paired and
alternate execution order; the aggregate report retains the paired external
overhead samples. It also includes per-depth and per-check medians and median
absolute deviations. The default output is
`capture/array-copy/z3-comparison.json`.

### 3. Run Light Review Benchmark Suite

For a more comprehensive evaluation with depth 10 (completes in less than 5 minutes):

```bash
# Build the benchmarking tool
cargo build -p garden --release

# Run light review configuration (depth 10, 20s timeout per benchmark)
./target/release/garden --config garden/benchmark_config.yaml --matrix light-review --output light_review_results.json
```

This runs all array benchmarks at depth 10 with both BMC Cost and Z3 array theory strategies, generating a JSON file with detailed results.

### Run a bounded external-corpus baseline

The external baseline config expects a local `external-benchmarks` directory or
symlink at the repository root. It recursively discovers VMT files and selects
the same 200-file sample on every run using a fixed seed. Before sampling, it
scans SMT-LIB applications and keeps only benchmarks with at least one array
read and one array write, so every selected problem exercises array reasoning. The
default matrix runs BMC Cost and concrete Z3 to depth 20 with eight workers and
a 10-second timeout per strategy/benchmark pair.

```bash
python3 main_eval.py \
  --env local \
  --benchmark-type external-depth20 \
  --config garden/external_benchmark_config.yaml \
  --name external-baseline-depth20
```

For a smaller smoke run or a different deterministic sample, invoke Garden
directly and override `--limit`, `--sample-seed`, or `--jobs`:

```bash
./target/release/garden \
  --config garden/external_benchmark_config.yaml \
  --matrix external-depth20 \
  --limit 20 \
  --sample-seed 20260806 \
  --jobs 4 \
  --output external_smoke.json
```

### 4. Use The Unified Evaluation Entry Point

`main_eval.py` is the top-level orchestration script for benchmark runs and reports.

```bash
# Capture every Garden result, replay it through matched stock and instrumented
# Z3 builds, and retain the comparison under one evaluation run.
uv run main_eval.py compare_with_instrumentation \
  --config benchmark_config.yml \
  --run-type small-eval \
  --run-id test-compare

# Generate the ordinary evaluation workbook with the instrumentation section.
uv run main_eval.py generate-report --run-id test-compare

# Local run with a combined workbook report
python3 main_eval.py \
  --env local \
  --benchmark-type deep-abstract \
  --benchmark-type deep-concrete \
  --name paper-smoke

# Iterate on a deterministic sample of benchmarks where either abstract
# BMC-cost or concrete exceeded 30 seconds (or timed out) in a prior run.
python3 main_eval.py \
  --env local \
  --benchmark-type deep-abstract-cone-then-full \
  --difficult-benchmarks <baseline-run-id> \
  --limit 8 \
  --sample-seed 0 \
  --name difficult-cone-smoke

# Evaluate the integrated formula transformations against the durable hard
# cases plus concrete-success/abstract-timeout cases derived from a baseline.
python3 main_eval.py \
  --env local \
  --benchmark-type formula-transformations \
  --formula-research-cohort <baseline-run-id> \
  --name formula-transformations

# AWS launch only: records a local run manifest and exits immediately
python3 main_eval.py \
  --env aws \
  --benchmark-type deep-abstract \
  --benchmark-type deep-concrete \
  --name paper-aws

# A separate capture run for local solver replay. Capture is deliberately
# opt-in because journal serialization and file I/O affect worker runtimes.
python3 main_eval.py \
  --env aws \
  --benchmark-type deep-abstract \
  --benchmark-type deep-concrete \
  --capture-solver-journals \
  --name paper-aws-captures

# Later, refresh status for an AWS-backed run
python3 main_eval.py --aws-run-id <run-id> --status

# When the AWS run is complete, download artifacts and build the report
python3 main_eval.py --aws-run-id <run-id> --generate-report

# Deep AWS runs also upload every incremental solver capture. Download those
# captures and replay completed sessions locally through the matched stock and
# instrumented Z3 builds.
python3 main_eval.py compare-downloaded-instrumentation \
  --run-id <run-id> \
  --z3-build-dir /path/to/z3-builder-output

# Regenerate the combined workbook with the local replay measurements.
python3 main_eval.py generate-report --run-id <run-id>
```

Passing `--difficult-benchmarks` without a run id selects the newest downloaded
`main_eval` run containing both abstract BMC-cost and concrete results. The
threshold defaults to 30 seconds and can be changed with
`--difficult-threshold-seconds`. The resolved source, complete cohort, and
selection reason for each benchmark are recorded in the new run manifest.

`--formula-research-cohort` combines the checked-in hard-tail wins, known
abstract Z3 regressions, and search-overhead cases with every benchmark where
concrete succeeds while abstract BMC-cost times out in the chosen baseline.
For this cohort, compare Z3 resource signals (`rlimit count`, decisions, added
equalities, clauses, and solver time) first. Raw abstract-instance count is a
diagnostic because frame unrolling and assertion deduplication deliberately
change how one abstract formula expands into solver assertions.

Phase-prefixed `abstract.*`, `concrete_validation.*`, and `total.*` statistics
are limited to the portable counters exposed by both Z3 and CVC5. Z3-only
signals such as `rlimit count`, `added eqs`, `mk clause`, and `mk bool var`
remain available under their backend-native names and are not synthesized for
CVC5 runs.

`compare_with_instrumentation` uses the benchmark selection and parameter matrix
named by `--run-type`. It builds Yardbird and Garden, captures each Z3-backed
solver session, enforces the captured SAT/UNSAT sequence during paired replay,
and writes the raw Garden JSON, captures, per-session comparison JSON, and
flattened comparison summary beneath
`benchmark_results/main_eval/<run-id>/`. If `--z3-build-dir` is omitted, the
command builds a matched Z3 pair under that run directory. It finds the
instrumented checkout from `--z3-checkout`, `YARDBIRD_Z3_CHECKOUT`, or a sibling
`z3` repository. Pass an existing builder output with `--z3-build-dir` to avoid
rebuilding.

The generated workbook retains the normal Garden strategy analysis and adds
paired stock/instrumented external timing, instrumentation overhead, and the
instrumented internal array-envelope versus non-array-residual breakdown. The
complete flattened data is exported as
`report/data/instrumentation_comparisons.csv`.

Artifacts are stored under `benchmark_results/main_eval/<run-id>/`. Raw benchmark JSON files land in per-matrix `raw/` directories using `MM_DD_YYYY_HH_MM.json` names, while generated figures and the Typst workbook live under `report/`.

AWS solver capture is disabled by default. With `--capture-solver-journals`,
workers run Garden with `--profile --solver-capture-root`, archive all capture
directories to S3, and preserve partial transcripts from timed-out benchmarks.
After download, captures are extracted beneath the run's `captures/<matrix>/`
directory. Only captures whose manifest is complete are replayed; unsuccessful
or interrupted results remain in the comparison summary as unavailable. Treat
the capture run's Yardbird runtimes as diagnostic rather than canonical; use a
separate capture-free run for end-to-end benchmark timing.

`--generate-report` also produces a self-contained analysis bundle:

- `report/workbook.pdf` includes solved counts, baseline coverage comparisons, runtime wins/losses, exclusive solves, and the largest improvements and regressions
- `report/analysis.json` contains the complete structured analysis
- `report/analysis.md` is a text-friendly summary
- `report/data/strategy_summary.csv` and `baseline_comparisons.csv` contain aggregate metrics
- `report/data/benchmark_results.csv` and `benchmark_comparisons.csv` contain normalized benchmark-level data for further exploration

The concrete strategy is selected as the comparison baseline when present. Shared runtimes within 5% are classified as ties, and missing strategy results are kept separate from unsuccessful results.

## Reproducing Paper Results

To fully reproduce the paper's evaluation:

```bash
cargo build --release -p yardbird
cargo build --release -p garden

# Run BMC Cost
./target/release/garden \
  --config garden/benchmark_config.yaml \
  --matrix deep-abstract \
  --output paper_results_abstract.json

# Run AST Size
./target/release/garden \
  --config garden/benchmark_config.yaml \
  --matrix deep-abstract-ast \
  --output paper_results_ast.json

# Run Z3 Array theory baseline
./target/release/garden \
  --config garden/benchmark_config.yaml \
  --matrix deep-concrete \
  --output paper_results_z3.json

# Run Z3 MBQI
./target/release/garden \
  --config garden/benchmark_config.yaml \
  --matrix  deep-abstract-with-quantifiers \
  --output paper_results_mbqi.json
```

Each of these runs will take 1.5 to 2 hours on an AWS EC2 instance. Times may vary locally and by hardware.

These 4 runs will reproduce the main results from the paper. The additional cost functions can be run
in a similar way: `deep-abstract-prefer-write`, `deep-abstract-prefer-constants`, `deep-abstract-prefer-read`.

### Functional Badge Criteria

#### 1. Documentation and Inventory

**Is the artifact documented with an inventory of artifacts and sufficient description to enable exercise?**

**YES.** Complete inventory:

- **Core Tool**: `src/` - Yardbird

  - `src/main.rs` - CLI entry point
  - `src/driver.rs` - Verification orchestration
  - `src/strategies/` - Proof strategies (abstract, concrete)
  - `src/cost_functions/` - Heuristics for term selection
  - `src/z3_ext.rs`, `src/vmt_bmc_session.rs` - Z3 integration and VMT BMC session state

- **Parsing Library**: `smt2parser/` - VMT and SMT2 parsing with array abstraction

- **Benchmarking Suite**: `garden/` - Automated benchmark runner

  - Configuration-driven execution
  - Supports parameter matrices
  - JSON output with metadata

- **Examples**: `examples/array/` - paper VMT benchmark files

- **Large local test corpus**: `examples/svcomp-vmt-bench/` - locally generated
  VMT inputs used for Yardbird stress testing and AWS benchmark runs. Exact
  upstream revisions and conversion provenance are still pending; see the
  corpus README before publishing or redistributing it independently.

**Is the artifact consistent and relevant to the associated paper, contributing to its main results?**

**YES.** The artifact directly supports the paper's claims:

- **Main Claim**: Yardbird performs bounded model checking with cost-guided abstraction refinement

  - Implemented in `src/strategies/abstract.rs` using egg-based term rewriting
  - Cost functions in `src/cost_functions/` implement heuristics discussed in paper

- **Evaluation Results**: All paper benchmarks are included in `examples/array/`

  - The `garden` tool reproduces the exact parameter configurations from the paper
  - Configuration `deep-abstract` matches paper's main evaluation (depth 50, 120s timeout)
  - All "deep" configurations in `garden/benchmark_config.yaml` when run with garden will replicate results given in the paper

- **Comparison with Baselines**:

  - Concrete strategy (`src/strategies/concrete.rs`) implements baseline approach

- **Performance Claims**: Quantifier instantiation counts and runtimes are logged and can be reproduced and verified from the output
  JSON file.

#### 3. Completeness

**Is the artifact complete, with all components relevant to the paper included?**

**YES.** All paper components are included:

- All benchmarks from evaluation section
- All strategies discussed (abstract, concrete)
- All cost functions evaluated (bmc-cost, ast-size, prefer-read, prefer-write, prefer-constants)
- Complete source code (no proprietary components)
- Benchmark runner to reproduce all experiments

#### 4. Runnability

**Can the software be executed successfully and can data be accessed and manipulated?**

**YES.** Multiple execution modes:

1. **Direct CLI**: `cargo run -- --filename <file> [options]`

   Exact `select(store(A, i, v), i)` preprocessing is disabled by default. Enable
   it explicitly with `--preprocess-exact-read-after-write`.
2. **Benchmark Suite**: `garden --config <yaml> --matrix <name>`

All benchmarks are accessible VMT files in `examples/`. Results are output as:

- Human-readable logs to stdout
- Structured JSON for automated processing
- Compatible with graphics generation pipeline

### Reusable Badge Criteria

#### 1. License for Reuse

**Does the artifact have a license allowing reuse and repurposing?**

**YES.** This project is licensed under the **MIT License** (see `LICENSE` file), which allows:

**Special provision for artifact evaluation:**
The `LICENSE` file includes an explicit addendum granting artifact evaluation committees the right to download, execute, modify, and redistribute the artifact for evaluation purposes.

All dependencies are also permissively licensed:

- Rust standard library: MIT/Apache-2.0
- Z3: MIT
- egg (e-graphs): MIT

#### 2. Dependencies Documentation

**Are all dependencies and libraries well documented and up to date?**

**YES.** Complete dependency documentation:

**System Dependencies:**

- Rust 1.89.0 (specified in `rust-toolchain.toml`)
- Z3 SMT solver 4.15.2+ (any modern version compatible)
- libclang-dev (for Z3 bindings)
- Standard build tools (gcc/clang, cmake)

**Rust Dependencies:** (all pinned in `Cargo.lock`)

- `z3 = "0.8"` - Z3 solver bindings
- `egg = "0.9"` - E-graph library for term rewriting
- Full list in `Cargo.toml`

#### 3. Usage Beyond the Paper

**Does the README explain how the artifact can be used beyond the paper?**

**YES.** Multiple extension points:

**1. Verify New Programs:**

```bash
# Create your own VMT file describing a transition system
# Run yardbird on it
cargo run --release -- --filename my_program.vmt --depth 20
```

**2. Add New Cost Functions:**

Implement the `egg::CostFunction` trait in `src/cost_functions/`:

```rust
pub trait CostFunction {
    fn cost(&self, enode: &ENode) -> Cost;
    fn name(&self) -> &str;
}
```

Example: `src/cost_functions/ast_size.rs` shows a simple implementation.

Register in `src/main.rs` to make it available via `--cost-function` flag.

**3. Extend with New Strategies:**

Add to `src/strategies/` following the pattern in `abstract.rs` or `concrete.rs`. Strategies coordinate:

- SMT problem construction
- Incremental solving
- Abstraction refinement

**4. Benchmark New Tool Configurations:**

Create custom YAML configs in `garden/`:

```yaml
parameter_matrices:
  my_experiment:
    depths: [10, 20, 30]
    strategies: ["my-new-strategy"]
    cost_functions: ["my-cost-function"]
    timeout_seconds: 60
```

Run with: `garden --config my_config.yaml --matrix my_experiment`

**5. Integration with Other Tools:**

- Use `--print-vmt` to output abstracted transition systems
- We can dump the solver state to SMTLIB2 at any time during execution, giving us the
  ability to use other solvers or tools.

#### 4. Documented Interfaces and Open Source

**Does the artifact provide documented interfaces for extensions, or is it open source?**

**YES, both:**

1. **Open Source**: Complete source code available, no proprietary components

2. **Documented Extension Interfaces:**

   - **Cost Functions**: `CostFunction` trait in `src/cost_functions/mod.rs`
   - **Strategies**: Pattern established in `src/strategies/`
   - **Output Formats**: JSON schema in `garden/src/main.rs`
   - **VMT Parsing**: Public API in `smt2parser/`

#### 5. Cross-Environment Usage

**Can the artifact be used in different environments (different systems, outside VM)?**

**YES.**

- Z3 is available on all major platforms and available through a python package with necessary header files
- Rust provides consistent cross-platform builds
- VMT files are platform-independent text files
- No OS-specific system calls or dependencies

# Running Example

`cargo run -- --filename examples/array/array_copy.vmt`

# IC3IA

If `ic3ia` binary is located in your system PATH, you can run

```
cargo run -- --filename examples/array/array_copy.vmt --invoke-ic3ia --print-vmt
```

This gives you the IC3IA output on the decorated transition system generated by yardbird.

# Performance Sampling

We've found that using `samply` is a nice way to find out where yardbird is spending time.
Unsurprisingly, it spends a lot of time making Z3 calls, but we've still been able to get some
speedups by looking at the callgraphs graphs and heatmaps.

### If you don't have `samply` installed already

- `cargo install --locked samply`

### Running `yardbird` with `samply`

- `cargo build`

- `samply record ./target/debug/yardbird --filename examples/array/array_copy.vmt`

## Building on Linux

I encountered the following error when building on a Linux machine:

```
error: failed to run custom build command for `z3-sys v0.8.1`

Caused by:
  process didn't exit successfully: `/home/cole/Documents/yardbird/target/debug/build/z3-sys-6ba06f331cb40b8a/build-script-build` (exit status: 101)
  --- stdout
  cargo:rerun-if-changed=build.rs
  cargo:rerun-if-env-changed=Z3_SYS_Z3_HEADER
  cargo:rerun-if-changed=wrapper.h
  cargo:rerun-if-env-changed=TARGET
  cargo:rerun-if-env-changed=BINDGEN_EXTRA_CLANG_ARGS_x86_64-unknown-linux-gnu
  cargo:rerun-if-env-changed=BINDGEN_EXTRA_CLANG_ARGS_x86_64_unknown_linux_gnu
  cargo:rerun-if-env-changed=BINDGEN_EXTRA_CLANG_ARGS

  --- stderr

  thread 'main' panicked at /home/cole/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/bindgen-0.66.1/lib.rs:604:31:
  Unable to find libclang: "couldn't find any valid shared libraries matching: ['libclang.so', 'libclang-*.so', 'libclang.so.*', 'libclang-*.so.*'], set the `LIBCLANG_PATH` environment variable to a path where one of these files can be found (invalid: [])"
  note: run with `RUST_BACKTRACE=1` environment variable to display a backtrace

```

This was resolved by running:

```
sudo apt install libclang-dev
```
