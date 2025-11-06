# Yardbird

This chicken lays `egg`s...

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

# Build yardbird
cargo build -p yardbird --release

# Verify build
./target/release/yardbird --help
```

### 2. Run a Single Example

This will automatically use the BMC Cost strategy.

```bash
# Run on a simple array copy example (completes in ~1 second)
./target/release/yardbird --filename examples/array/array_copy.vmt --depth 10
```

### 3. Run Light Review Benchmark Suite

For a more comprehensive evaluation with depth 10 (completes in less than 5 minutes):

```bash
# Build the benchmarking tool
cargo build -p garden --release

# Run light review configuration (depth 10, 20s timeout per benchmark)
./target/release/garden --config garden/benchmark_config.yaml --matrix light-review --output light_review_results.json
```

This runs all array benchmarks at depth 10 with both BMC Cost and Z3 array theory strategies, generating a JSON file with detailed results.

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
  - `src/z3_ext.rs`, `src/smt_problem.rs` - Z3 integration

- **Parsing Library**: `smt2parser/` - VMT and SMT2 parsing with array abstraction

- **Benchmarking Suite**: `garden/` - Automated benchmark runner

  - Configuration-driven execution
  - Supports parameter matrices
  - JSON output with metadata

- **Examples**: `examples/array/` - VMT benchmark files

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
