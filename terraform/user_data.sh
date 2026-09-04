#!/bin/bash
set -e
exec > >(tee /var/log/user-data.log) 2>&1

# Function to log and upload status to S3
log_status() {
    local status="$1"
    local message="$2"
    echo "[$status] $(date): $message"
    echo "[$status] $(date): $message" | aws s3 cp - s3://${s3_bucket_name}/benchmarks/${unique_benchmark_name}/status.log --region us-east-2 || true
}

# Function to upload logs to S3
upload_logs() {
    aws s3 cp /var/log/user-data.log s3://${s3_bucket_name}/benchmarks/${unique_benchmark_name}/user-data.log --region us-east-2 || true
}

# Trap to upload logs on exit
trap upload_logs EXIT

log_status "INFO" "Starting Yardbird benchmark setup"

# Install dependencies
log_status "INFO" "Installing system dependencies"
apt-get update
if ! apt-get install -y git curl cmake build-essential python3 awscli pkg-config libssl-dev libclang-dev software-properties-common openjdk-17-jre-headless; then
    log_status "ERROR" "Failed to install system dependencies"
    exit 1
fi

# Z3 4.16 uses the C++20 <format> header, which is unavailable in the GCC 11
# toolchain shipped by Ubuntu 22.04. Install GCC 13 before compiling the
# vendored Z3 source selected in Cargo.toml.
log_status "INFO" "Installing GCC 13 for Z3 4.16"
if ! add-apt-repository -y ppa:ubuntu-toolchain-r/test || \
   ! apt-get update || \
   ! apt-get install -y gcc-13 g++-13; then
    log_status "ERROR" "Failed to install GCC 13"
    exit 1
fi

if ! printf '#include <format>\n' | g++-13 -std=c++20 -x c++ -fsyntax-only -; then
    log_status "ERROR" "GCC 13 does not provide the C++20 <format> header"
    exit 1
fi

# Setup ubuntu user environment first
log_status "INFO" "Setting up ubuntu user environment"
chown -R ubuntu:ubuntu /home/ubuntu

# Install Rust as ubuntu user
sudo -u ubuntu bash << 'EOF'
set -e

# Force z3-sys/CMake to use a compiler with C++20 <format> support.
export CC=gcc-13
export CXX=g++-13

# Function to log inside ubuntu user context
log_status() {
    local status="$1"
    local message="$2"
    echo "[$status] $(date): $message"
}

cd /home/ubuntu

# Install Rust as ubuntu user
log_status "INFO" "Installing Rust as ubuntu user"
if ! curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y; then
    log_status "ERROR" "Failed to install Rust"
    exit 1
fi

# Source cargo environment
source ~/.cargo/env

log_status "INFO" "Using $(${CXX} --version | head -n 1) to build vendored Z3"

# Clone repository
log_status "INFO" "Cloning yardbird repository"
if ! git clone https://github.com/cvick32/yardbird.git; then
    log_status "ERROR" "Failed to clone repository"
    exit 1
fi
cd yardbird

log_status "INFO" "Updating to the latest origin/main"
if ! git checkout main || ! git pull --ff-only origin main; then
    log_status "ERROR" "Failed to update to the latest origin/main"
    exit 1
fi

benchmark_config_path=${repository_benchmark_config}
if [ ! -f "$benchmark_config_path" ]; then
    log_status "ERROR" "Benchmark configuration not found: $benchmark_config_path"
    exit 1
fi

log_status "INFO" "Using Yardbird commit $(git rev-parse HEAD)"

log_status "INFO" "Building yardbird"
if ! cargo build --release -p yardbird --no-default-features; then
    log_status "ERROR" "Failed to build yardbird binary"
    exit 1
fi

log_status "INFO" "Building garden"
if ! cargo build --release -p garden --no-default-features; then
    log_status "ERROR" "Failed to build garden binary"
    exit 1
fi

# Verify garden binary exists
if [ ! -f "./target/release/garden" ]; then
    log_status "ERROR" "Garden binary not found after build"
    exit 1
fi
log_status "INFO" "Garden binary built successfully"

echo "$(cat "$benchmark_config_path")"

log_status "INFO" "Running benchmarks with garden"
capture_root="benchmark_captures_${unique_benchmark_name}"
capture_args=()
garden_args=(${garden_args})
if [ "${capture_solver_journals}" = "true" ]; then
    capture_args=(--profile --solver-capture-root "$capture_root")
    log_status "INFO" "Solver journal capture is enabled"
else
    log_status "INFO" "Solver journal capture is disabled"
fi
if ! ./target/release/garden \
    --config "$benchmark_config_path" \
    --matrix ${matrix_name} \
    --output benchmark_results_${unique_benchmark_name}.json \
    "${garden_args[@]}" \
    "${capture_args[@]}"; then
    log_status "ERROR" "Benchmark execution failed"
    exit 1
fi

# Verify benchmark results file exists
if [ ! -f "benchmark_results_${unique_benchmark_name}.json" ]; then
    log_status "ERROR" "Benchmark results file not found"
    exit 1
fi
log_status "INFO" "Benchmarks completed successfully"

# Upload results
log_status "INFO" "Uploading results to S3"
if ! aws s3 cp benchmark_results_${unique_benchmark_name}.json s3://${s3_bucket_name}/benchmarks/${unique_benchmark_name}/results.json --region us-east-2; then
    log_status "ERROR" "Failed to upload benchmark results"
    exit 1
fi
if [ "${capture_solver_journals}" = "true" ]; then
    # Preserve every solver journal, including incomplete captures from timed-out
    # benchmark processes. Archive the contents rather than the dynamic root name
    # so the controller can extract into its per-matrix capture directory.
    log_status "INFO" "Archiving solver captures"
    capture_archive="benchmark_captures_${unique_benchmark_name}.tar.gz"
    if ! tar -C "$capture_root" -czf "$capture_archive" .; then
        log_status "ERROR" "Failed to archive solver captures"
        exit 1
    fi
    if ! aws s3 cp "$capture_archive" s3://${s3_bucket_name}/benchmarks/${unique_benchmark_name}/captures.tar.gz --region us-east-2; then
        log_status "ERROR" "Failed to upload solver captures"
        exit 1
    fi
fi

# Mark completion
log_status "INFO" "Marking completion"
echo "Benchmark completed at $(date)" | aws s3 cp - s3://${s3_bucket_name}/benchmarks/${unique_benchmark_name}/completion.txt --region us-east-2

log_status "INFO" "Setup and benchmark complete"
EOF

# Terminate instance
sudo shutdown -h now
