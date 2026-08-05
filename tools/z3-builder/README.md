# Z3 builder

This tool builds two Z3 executables for offline comparison:

- **stock**: the pristine Z3 revision pinned by Yardbird;
- **instrumented**: a local Z3 checkout containing our profiling changes.

Both builds receive the same compiler and CMake flags. After building, the tool
runs both executables over the same small SMT-LIB suite and requires identical
ordered results. It records the commands, source revisions, whether the local
checkout was dirty, results, and diagnostic timings in `manifest.json`.

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

The output directory must not already exist. Build progress goes to stderr and
the completed `manifest.json` is also emitted as one JSON object on stdout, so a
capture can be replayed immediately through both binaries:

```bash
python3 tools/z3-builder/z3_builder.py \
  --z3-checkout /path/to/z3 \
  --instrumented-checkout /path/to/instrumented-z3 \
  --output /tmp/yardbird-z3-build |
  python3 tools/z3_array_probe.py replay \
    --capture-dir capture/array-copy
```

Timings from the bundled smoke tests are diagnostic only, not benchmark
results. An existing build can be replayed again with
`--z3-build-dir /tmp/yardbird-z3-build`.
