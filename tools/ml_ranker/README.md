# Yardbird ML Ranker

This directory contains the training script for Yardbird's array-term
`logistic-regression` cost function. It exports candidate rows from the Yardbird
PostgreSQL database, trains a small weighted logistic regression model with
`numpy`, and writes the JSON model consumed by the Rust runtime.

The tool is deliberately lightweight. Runtime dependencies are managed by `uv`
in this directory and currently consist of Python 3.11+ plus `numpy`; data export
also requires the `psql` CLI.

## Label

The current label is candidate-level direct core membership:

- A decision is core-positive when it is linked to an abstract instantiation
  whose `abstract_instantiations.in_unsat_core` flag is true.
- Within a core-positive decision, the candidate that Yardbird chose is labeled
  positive.
- All other candidates are labeled negative.

This is a conservative per-slot signal. It does not try to infer which earlier
instantiations enabled later core-relevant terms.

## Train

From the repository root:

```bash
uv run --project tools/ml_ranker \
  python tools/ml_ranker/train_ranker.py \
  --out-dir tmp/ml-ranker/direct-core-smoke
```

`train_ranker.py` defaults to the local
`tools/ml_ranker/array-family-v1.yaml` manifest. Pass `--manifest <path>` to use
another family split manifest.

The database URL is resolved in this order:

- `--database-url`
- `YARDBIRD_DATABASE_URL` from the environment or repo-root `.env`
- `DATABASE_URL` from the environment or repo-root `.env`

Useful options:

- `--include-unsuccessful`: include benchmark runs where `benchmarks.success` is
  not true.
- `--epochs`, `--learning-rate`, `--l2`, `--positive-weight`: logistic
  regression training hyperparameters.

## Outputs

The output directory contains:

- `dataset-summary.json`: manifest coverage and extracted row counts by split.
- `metrics.json`: model ranking metrics compared with the current-cost
  baseline for each split.
- `model.json`: learned weights, numeric normalization stats, and the one-hot
  categorical vocabulary used by Yardbird at runtime.

Ranking metrics are computed only for decisions with at least one positive
candidate. Negative-only decisions still contribute training examples.

## Evaluate In Yardbird

Use the trained `model.json` as the `logistic-regression` cost function:

```bash
cargo run -- -f examples/array/array_copy.vmt \
  --strategy abstract \
  --cost-function logistic-regression \
  --ranker-model tmp/ml-ranker/direct-core-smoke/model.json
```
