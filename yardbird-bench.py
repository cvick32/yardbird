#!/usr/bin/env python3

import argparse
import json
import subprocess
import sys
import tempfile
from datetime import datetime
from pathlib import Path


def run_command(cmd, cwd=None, check=True):
    """Run a command and return the result"""
    print(f"Running: {' '.join(cmd)}")
    result = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if check and result.returncode != 0:
        print(f"Command failed: {' '.join(cmd)}")
        print(f"stderr: {result.stderr}")
        sys.exit(1)
    return result


def build_yardbird():
    """Build yardbird and garden"""
    print("Building yardbird and garden...")
    run_command(["cargo", "build", "--release", "-p", "garden"])


def run_benchmarks_local(config_file, matrix=None, output_file=None):
    """Run benchmarks locally using garden"""
    cmd = ["./target/release/garden", "--config", str(config_file)]

    if matrix:
        cmd.extend(["--matrix", matrix])

    if output_file:
        cmd.extend(["--output", str(output_file)])

    run_command(cmd)
    return output_file


def generate_graphics(json_file, output_dir=None):
    """Generate graphics using paper-graphics"""
    if output_dir is None:
        output_dir = Path.cwd()

    print(f"Generating graphics from {json_file}...")

    # Parse JSON to get metadata for paper-graphics
    with open(json_file) as f:
        data = json.load(f)

    # Extract depth and timeout from first benchmark if available
    if data.get("benchmarks") and data["benchmarks"][0]["result"]:
        first_result = data["benchmarks"][0]["result"][0]
        depth = first_result["depth"]
        timeout = 30  # Default, should come from config
    else:
        depth = 10
        timeout = 30

    # Run paper-graphics
    run_command(
        ["uv", "run", "main.py", str(Path(json_file).absolute()), str(depth), str(timeout)],
        cwd="paper-graphics",
    )


def upload_to_s3(local_dir, s3_bucket, s3_prefix):
    """Upload results to S3"""
    print(f"Uploading results to s3://{s3_bucket}/{s3_prefix}")
    run_command(
        [
            "aws",
            "s3",
            "sync",
            str(local_dir),
            f"s3://{s3_bucket}/{s3_prefix}",
            "--exclude",
            "*.tmp",
        ]
    )


def run_ec2_benchmarks(config_file, matrix=None, s3_bucket=None):
    """Run benchmarks on EC2 instance"""
    if not s3_bucket:
        print("S3 bucket required for EC2 execution")
        sys.exit(1)

    # Use the EC2 runner script
    cmd = [
        "python3",
        "scripts/ec2_runner.py",
        str(config_file),
        "--matrix",
        matrix,
        "--s3-bucket",
        s3_bucket,
        "--wait",
    ]

    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        print(f"EC2 execution failed: {result.stderr}")
        return None

    print("EC2 benchmarks completed")
    return None


def main():
    parser = argparse.ArgumentParser(description="Yardbird Benchmarking Platform")
    parser.add_argument("config", help="Benchmark configuration file")
    parser.add_argument("--matrix", help="Specific matrix to run (default: all)")
    parser.add_argument("--output", help="Output JSON file (default: timestamped)")
    parser.add_argument(
        "--graphics", action="store_true", help="Generate graphics after benchmarking"
    )
    parser.add_argument("--upload", help="S3 bucket to upload results to")
    parser.add_argument(
        "--ec2", action="store_true", help="Run on EC2 instead of locally"
    )
    parser.add_argument(
        "--build", action="store_true", default=True, help="Build before running"
    )

    args = parser.parse_args()

    config_file = Path(args.config)
    if not config_file.exists():
        print(f"Config file not found: {config_file}")
        sys.exit(1)

    # Generate timestamped output filename if not provided
    if args.output:
        output_file = Path(args.output)
    else:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        matrix_suffix = f"_{args.matrix}" if args.matrix else ""
        output_file = Path(f"benchmark_results_{timestamp}{matrix_suffix}.json")

    # Build if requested
    if args.build:
        build_yardbird()

    # Run benchmarks
    if args.ec2:
        result_file = run_ec2_benchmarks(config_file, args.matrix, args.upload)
    else:
        result_file = run_benchmarks_local(config_file, args.matrix, output_file)

    if not result_file or not Path(result_file).exists():
        print("No results file generated")
        sys.exit(1)

    # Generate graphics if requested
    if args.graphics:
        generate_graphics(result_file)

    # Upload to S3 if requested
    if args.upload:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        s3_prefix = f"benchmarks/{timestamp}"

        # Create temporary directory with all artifacts
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_path = Path(temp_dir)

            # Copy JSON results
            subprocess.run(["cp", str(result_file), str(temp_path / "results.json")])

            # Copy any generated graphics
            for png_file in Path.cwd().glob("*.png"):
                subprocess.run(["cp", str(png_file), str(temp_path)])

            upload_to_s3(temp_path, args.upload, s3_prefix)
            print(f"Results uploaded to s3://{args.upload}/{s3_prefix}")

    print(f"Benchmarking complete! Results in: {result_file}")


if __name__ == "__main__":
    main()
