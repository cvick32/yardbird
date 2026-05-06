#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SYNTH_DIR="$ROOT_DIR/benchmark-synth"
CORPUS_NAME="${BENCHMARK_CORPUS_NAME:-default}"
OUTPUT_DIR="$SYNTH_DIR/generated/corpora/$CORPUS_NAME"
BENCHMARK_SEED="${BENCHMARK_SEED:-17}"
BENCHMARK_COUNT="${BENCHMARK_COUNT:-72}"
BENCHMARK_BUG_RATIO="${BENCHMARK_BUG_RATIO:-0.30}"

cd "$SYNTH_DIR"

if [[ ! -d .venv ]]; then
  python3 -m venv .venv
fi

uv sync

rm -rf "$OUTPUT_DIR"

.venv/bin/benchmark-synth generate \
  --output-dir "$OUTPUT_DIR" \
  --seed "$BENCHMARK_SEED" \
  --count "$BENCHMARK_COUNT" \
  --bug-ratio "$BENCHMARK_BUG_RATIO"

echo "generated corpus: $OUTPUT_DIR"
echo "manifest: $OUTPUT_DIR/manifest.json"
find "$OUTPUT_DIR" -maxdepth 2 -type f | sort
