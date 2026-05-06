# Benchmark Synth

Semantics-first benchmark synthesis workspace for Yardbird.

## Setup

```bash
cd benchmark-synth
python -m venv .venv
source .venv/bin/activate
uv sync
```

The default regeneration path from the repo root is:

```bash
./benchmark-gen.sh
```

## Run Tests

```bash
cd benchmark-synth
source .venv/bin/activate
pytest
```

## Current Scope

The initial implementation provides:

- a typed semantic IR
- coarse benchmark metadata
- deterministic naming
- one `single_loop` `copy` family with multiple witnesses
- one bug mutator
- lowering to VMT
- corpus generation
- basic Yardbird execution support

## Example

```bash
PYTHONPATH=src python -m benchmark_synth.cli generate \
  --output-dir generated/corpora/dev \
  --seed 7 \
  --count 4 \
  --family copy \
  --skeleton single_loop \
  --property-family pointwise \
  --bug-ratio 0.5
```

If you omit `--family`, `--skeleton`, and `--property-family`, generation uses
the current supported structure mix.

## Inspect Generated Benchmarks

Generated corpora are written under `generated/corpora/<name>/`.

Typical files:

- benchmarks: `generated/corpora/dev/benchmarks/*.vmt`
- metadata: `generated/corpora/dev/metadata/*.json`
- manifest: `generated/corpora/dev/manifest.json`

Useful commands:

```bash
cd benchmark-synth
find generated/corpora/dev -maxdepth 2 -type f | sort
sed -n '1,200p' generated/corpora/dev/benchmarks/<benchmark>.vmt
cat generated/corpora/dev/metadata/<benchmark>.json
```

To try a generated benchmark in Yardbird:

```bash
cd ..
target/debug/yardbird \
  --filename benchmark-synth/generated/corpora/dev/benchmarks/<benchmark>.vmt \
  --strategy concrete \
  --depth 3 \
  --json-output
```

## Default Regeneration Script

`../benchmark-gen.sh` deletes the current default corpus and regenerates a new
mixed benchmark set with sensible defaults.

Defaults:

- output corpus: `generated/corpora/default`
- seed: `17`
- count: `72`
- bug ratio: `0.30`

You can override them with environment variables:

```bash
BENCHMARK_SEED=21 BENCHMARK_COUNT=96 BENCHMARK_BUG_RATIO=0.4 ./benchmark-gen.sh
```
