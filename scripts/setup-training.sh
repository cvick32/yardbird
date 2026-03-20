#!/bin/bash
# Setup script for Yardbird training data collection
# This script helps you get started with logging training data to Postgres

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

echo "=== Yardbird Training Setup ==="
echo ""

# Check for required tools
check_command() {
    if ! command -v "$1" &> /dev/null; then
        echo "Error: $1 is not installed"
        return 1
    fi
}

echo "Checking prerequisites..."
check_command cargo
check_command psql || echo "Warning: psql not found - you'll need to set up the database manually"
echo ""

# Create .env file if it doesn't exist
ENV_FILE="$PROJECT_ROOT/.env"
if [ ! -f "$ENV_FILE" ]; then
    echo "Creating .env file template..."
    cat > "$ENV_FILE" << 'EOF'
# Yardbird Training Configuration
# Update this with your Postgres connection string
YARDBIRD_DATABASE_URL=postgres://postgres:postgres@localhost:5432/yardbird_training
EOF
    echo "Created $ENV_FILE - please update with your database credentials"
else
    echo ".env file already exists"
fi
echo ""
echo ""
echo "  # Create database"
echo "  createdb yardbird_training"
echo ""
echo "  # Or with psql:"
echo "  psql -c 'CREATE DATABASE yardbird_training;'"
echo ""
echo "  # Run migrations (after building with training feature)"
echo "  psql -d yardbird_training -f $PROJECT_ROOT/src/training/migrations/001_initial.sql"
echo ""

# Build
echo "=== Building Yardbird ==="
echo ""
echo "Building yardbird with training feature..."
cd "$PROJECT_ROOT"
cargo build --release --features training
echo ""

echo "Building garden..."
cargo build --release -p garden
echo ""

echo "=== Setup Complete ==="
echo ""
echo "To collect training data, run:"
echo ""
echo "  # Single benchmark"
echo "  ./target/release/yardbird --train -f examples/array/array_copy.vmt"
echo ""
echo "  # Run garden on all benchmarks (with training)"
echo "  ./scripts/run-training.sh"
echo ""
echo "  # Or manually with garden:"
echo "  ./target/release/garden examples/array \\"
echo "    --strategy abstract \\"
echo "    --cost-function bmc-cost \\"
echo "    --depth 10 \\"
echo "    --timeout 60 \\"
echo "    -o results.json"
echo ""
echo "Garden can pass --train now. Example:"
echo "  cargo build --release -p garden --features training"
echo "  ./target/release/garden --config garden/benchmark_config.yaml --matrix quick --train"
