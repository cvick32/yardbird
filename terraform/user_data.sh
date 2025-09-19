#!/bin/bash
set -e
exec > >(tee /var/log/user-data.log) 2>&1

# Function to log and upload status to S3
log_status() {
    local status="$1"
    local message="$2"
    echo "[$status] $(date): $message"
    echo "[$status] $(date): $message" | aws s3 cp - s3://${s3_bucket_name}/benchmarks/${timestamp}/status.log --region us-east-2 || true
}

# Function to upload logs to S3
upload_logs() {
    aws s3 cp /var/log/user-data.log s3://${s3_bucket_name}/benchmarks/${timestamp}/user-data.log --region us-east-2 || true
}

# Trap to upload logs on exit
trap upload_logs EXIT

log_status "INFO" "Starting Yardbird benchmark setup"

# Install dependencies
log_status "INFO" "Installing system dependencies"
apt-get update
if ! apt-get install -y git curl build-essential python3 python3-pip awscli pkg-config libssl-dev libclang-dev libz3-dev; then
    log_status "ERROR" "Failed to install system dependencies"
    exit 1
fi

# Setup ubuntu user environment first
log_status "INFO" "Setting up ubuntu user environment"
chown -R ubuntu:ubuntu /home/ubuntu

# Install Rust and uv as ubuntu user
sudo -u ubuntu bash << 'EOF'
set -e

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

# Install uv as ubuntu user
log_status "INFO" "Installing uv for Python dependency management"
if ! curl -LsSf https://astral.sh/uv/install.sh | sh; then
    log_status "ERROR" "Failed to install uv"
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

log_status "INFO" "Building yardbird (garden)"
if ! cargo build --release -p garden; then
    log_status "ERROR" "Failed to build garden binary"
    exit 1
fi

# Verify garden binary exists
if [ ! -f "./target/release/garden" ]; then
    log_status "ERROR" "Garden binary not found after build"
    exit 1
fi
log_status "INFO" "Garden binary built successfully"

# Write config file
log_status "INFO" "Writing benchmark config file"
cat > garden/run_config.yaml << 'CONFIG_EOF'
${config_content}
CONFIG_EOF

# Validate config file exists
if [ ! -f "garden/run_config.yaml" ]; then
    log_status "ERROR" "Config file was not created successfully"
    exit 1
fi

log_status "INFO" "Running benchmarks with garden"
if ! ./target/release/garden --config garden/run_config.yaml --matrix ${matrix_name} --output benchmark_results_${timestamp}.json; then
    log_status "ERROR" "Benchmark execution failed"
    exit 1
fi

# Verify benchmark results file exists
if [ ! -f "benchmark_results_${timestamp}.json" ]; then
    log_status "ERROR" "Benchmark results file not found"
    exit 1
fi
log_status "INFO" "Benchmarks completed successfully"

# Generate graphics
log_status "INFO" "Generating graphics"
cd paper-graphics
if ! uv run main.py ../benchmark_results_${timestamp}.json 10 30; then
    log_status "ERROR" "Failed to generate main graphics"
    cd ..
    # Continue with upload even if graphics fail
else
    if ! uv run tikz_generator.py ../benchmark_results_${timestamp}.json --all; then
        log_status "ERROR" "Failed to generate tikz graphics"
    else
        log_status "INFO" "Graphics generated successfully"
    fi
    cd ..
fi

# Upload results
log_status "INFO" "Uploading results to S3"
if ! aws s3 cp benchmark_results_${timestamp}.json s3://${s3_bucket_name}/benchmarks/${timestamp}/results.json --region us-east-2; then
    log_status "ERROR" "Failed to upload benchmark results"
    exit 1
fi

if ! aws s3 sync paper-graphics/ s3://${s3_bucket_name}/benchmarks/${timestamp}/graphics/ --exclude "*.py" --exclude "*.toml" --exclude "*.md" --exclude "*.lock" --region us-east-2; then
    log_status "ERROR" "Failed to upload graphics"
else
    log_status "INFO" "Graphics uploaded successfully"
fi

# Mark completion
log_status "INFO" "Marking completion"
echo "Benchmark completed at $(date)" | aws s3 cp - s3://${s3_bucket_name}/benchmarks/${timestamp}/completion.txt --region us-east-2

log_status "INFO" "Setup and benchmark complete"
EOF

# Terminate instance
sudo shutdown -h now