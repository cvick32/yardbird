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
if ! apt-get install -y git curl cmake build-essential python3 python3-pip awscli pkg-config libssl-dev libclang-dev; then
    log_status "ERROR" "Failed to install system dependencies"
    exit 1
fi



# Setup ubuntu user environment first
log_status "INFO" "Setting up ubuntu user environment"
chown -R ubuntu:ubuntu /home/ubuntu

# Install Rust as ubuntu user
sudo -u ubuntu bash << 'EOF'
set -e

# install Z3
pip install z3-solver==4.15.3
sudo cp /home/ubuntu/.local/lib/python3.10/site-packages/z3/lib/* /usr/local/lib/
export LD_LIBRARY_PATH="/home/ubuntu/.local/lib/python3.10/site-packages/z3/lib/"

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

# Clone repository
log_status "INFO" "Cloning yardbird repository"
if ! git clone https://github.com/cvick32/yardbird.git; then
    log_status "ERROR" "Failed to clone repository"
    exit 1
fi
cd yardbird

echo git log -1 --format="%H"

log_status "INFO" "Building yardbird"
if ! Z3_SYS_Z3_HEADER="/home/ubuntu/.local/lib/python3.10/site-packages/z3/include/z3.h" cargo build --release -p yardbird; then
    log_status "ERROR" "Failed to build yardbird binary"
    exit 1
fi

log_status "INFO" "Building garden"
if ! Z3_SYS_Z3_HEADER="/home/ubuntu/.local/lib/python3.10/site-packages/z3/include/z3.h" cargo build --release -p garden; then
    log_status "ERROR" "Failed to build garden binary"
    exit 1
fi

# Verify garden binary exists
if [ ! -f "./target/release/garden" ]; then
    log_status "ERROR" "Garden binary not found after build"
    exit 1
fi
log_status "INFO" "Garden binary built successfully"

echo "$(cat garden/benchmark_config.yaml)"

log_status "INFO" "Running benchmarks with garden"
if ! ./target/release/garden --config garden/benchmark_config.yaml --matrix ${matrix_name} --output benchmark_results_${unique_benchmark_name}.json; then
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

# Mark completion
log_status "INFO" "Marking completion"
echo "Benchmark completed at $(date)" | aws s3 cp - s3://${s3_bucket_name}/benchmarks/${unique_benchmark_name}/completion.txt --region us-east-2

log_status "INFO" "Setup and benchmark complete"
EOF

# Terminate instance
sudo shutdown -h now