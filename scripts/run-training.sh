#!/bin/bash
# Run training data collection on array benchmarks
# This runs yardbird with --train flag on all examples

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

# Load .env file
if [ -f "$PROJECT_ROOT/.env" ]; then
    export $(grep -v '^#' "$PROJECT_ROOT/.env" | xargs)
fi

# Configuration
EXAMPLES_DIR="${1:-$PROJECT_ROOT/examples/array}"
DEPTH="${DEPTH:-10}"
TIMEOUT="${TIMEOUT:-60}"
COST_FUNCTIONS="${COST_FUNCTIONS:-bmc-cost ast-size prefer-read prefer-write prefer-constants}"
STRATEGY="${STRATEGY:-abstract}"

# Check database URL
if [ -z "$YARDBIRD_DATABASE_URL" ]; then
    echo "Error: YARDBIRD_DATABASE_URL not set"
    echo "Please create a .env file with your database URL or set the environment variable"
    exit 1
fi

# Check yardbird binary
YARDBIRD="$PROJECT_ROOT/target/release/yardbird"
if [ ! -f "$YARDBIRD" ]; then
    echo "Yardbird binary not found. Building..."
    cd "$PROJECT_ROOT"
    cargo build --release --features training
fi

echo "=== Training Data Collection ==="
echo "Examples: $EXAMPLES_DIR"
echo "Depth: $DEPTH"
echo "Timeout: ${TIMEOUT}s"
echo "Strategy: $STRATEGY"
echo "Cost functions: $COST_FUNCTIONS"
echo "Database: ${YARDBIRD_DATABASE_URL%%@*}@..." # Hide password
echo ""

# Count examples
EXAMPLES=($(find "$EXAMPLES_DIR" -name "*.vmt" | sort))
TOTAL=${#EXAMPLES[@]}
echo "Found $TOTAL benchmarks"
echo ""

# Stats
SUCCESS=0
FAILED=0
TIMEOUT_COUNT=0

# Run each benchmark with each cost function
for COST_FN in $COST_FUNCTIONS; do
    echo "=== Cost Function: $COST_FN ==="

    COUNT=0
    for EXAMPLE in "${EXAMPLES[@]}"; do
        COUNT=$((COUNT + 1))
        BASENAME=$(basename "$EXAMPLE" .vmt)

        printf "[%3d/%d] %-40s " "$COUNT" "$TOTAL" "$BASENAME"

        # Run with timeout
        START=$(date +%s)
        if timeout "$TIMEOUT" "$YARDBIRD" \
            --train \
            --strategy "$STRATEGY" \
            --cost-function "$COST_FN" \
            --depth "$DEPTH" \
            --track-instantiations \
            -f "$EXAMPLE" \
            > /dev/null 2>&1; then

            END=$(date +%s)
            ELAPSED=$((END - START))
            echo "OK (${ELAPSED}s)"
            SUCCESS=$((SUCCESS + 1))
        else
            EXIT_CODE=$?
            if [ $EXIT_CODE -eq 124 ]; then
                echo "TIMEOUT"
                TIMEOUT_COUNT=$((TIMEOUT_COUNT + 1))
            else
                echo "FAILED ($EXIT_CODE)"
                FAILED=$((FAILED + 1))
            fi
        fi
    done
    echo ""
done

# Summary
TOTAL_RUNS=$((SUCCESS + FAILED + TIMEOUT_COUNT))
echo "=== Summary ==="
echo "Total runs: $TOTAL_RUNS"
echo "Success: $SUCCESS"
echo "Failed: $FAILED"
echo "Timeout: $TIMEOUT_COUNT"
echo ""
echo "Training data has been logged to the database."
echo "Query with: psql \$YARDBIRD_DATABASE_URL -c 'SELECT COUNT(*) FROM benchmarks;'"
