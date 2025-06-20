# Yardbird

This chicken lays `egg`s...

# Benchmark Results

[Scarecrow](https://scarecrow.sgt-pl.com/)

# Running Example

`cargo run -- --filename examples/array_copy.vmt`

# IC3IA

If `ic3ia` binary is located in your system PATH, you can run

```
cargo run -- --filename examples/array_copy.vmt --invoke-ic3ia --print-vmt
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

- `samply record ./target/debug/yardbird --filename examples/array_copy.vmt`

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

# notes

measure if first forall requires a model if it takes a long time for MBQI to get a model

just use a trigger based instantiation scheme for insts where we need quantifiers

NO EXPLANATIONS: cargo run -- --filename examples/array_copy.vmt -d 300  5.43s user 0.11s system 90% cpu 6.100 total

W EXPLANATIONS:  cargo run -- --filename examples/array_copy.vmt -d 300  5.27s user 0.17s system 48% cpu 11.230 total