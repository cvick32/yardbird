# Z3 builder

This tool builds two Z3 executables for offline comparison:

- **stock**: the pristine Z3 revision pinned by Yardbird;
- **instrumented**: a local Z3 checkout containing our profiling changes.

Both builds receive the same compiler and CMake flags. After building, the tool
runs both executables over the same small SMT-LIB suite and requires identical
ordered results. It records the commands, source revisions, patch hash, binary
hashes, results, and diagnostic timings in `manifest.json`.

Yardbird does not link against the instrumented build. These executables are
intended to replay SMT-LIB sessions captured from Yardbird.

## Run it

The stock checkout must contain the pinned commit. If `--instrumented-checkout`
is omitted, the same checkout is used and any local changes in it become the
instrumented build.

```bash
python3 tools/z3-builder/z3_builder.py \
  --z3-checkout /path/to/z3 \
  --output /tmp/yardbird-z3-build
```

With a separate checkout for instrumentation work:

```bash
python3 tools/z3-builder/z3_builder.py \
  --z3-checkout /path/to/z3 \
  --instrumented-checkout /path/to/instrumented-z3 \
  --output /tmp/yardbird-z3-build
```

The output directory must not already exist. The command prints
`Z3_STOCK_BIN` and `Z3_INSTRUMENTED_BIN`; those paths can later be passed to the
Yardbird replay/comparison tool. Timings from the bundled smoke tests are
diagnostic only, not benchmark results.
