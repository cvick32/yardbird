#!/usr/bin/env python3

import subprocess
import json
import argparse
import time
import boto3
from pathlib import Path
from datetime import datetime

TERRAFORM_DIR = Path(__file__).parent / "terraform"


def run_terraform_command(cmd, cwd=None):
    """Run terraform command"""
    print(f"Running: terraform {' '.join(cmd)}")
    result = subprocess.run(
        ["terraform"] + cmd, cwd=cwd, capture_output=True, text=True
    )
    if result.returncode != 0:
        print(f"Terraform command failed: {result.stderr}")
        return None
    return result.stdout


def launch_benchmark_instance(config_file, matrix_name, terraform_outputs):
    """Launch instance using deployed infrastructure"""

    # Read config
    with open(config_file) as f:
        config_content = f.read()

    ec2 = boto3.client("ec2", region_name="us-east-2")  # Use us-east-2 for key pairs

    unique_benchmark_name = f"{matrix_name}-{datetime.now().strftime('%Y%m%d_%H%M%S')}"

    # Read user data template and substitute variables

    user_data_template_path = TERRAFORM_DIR / "user_data.sh"

    with open(user_data_template_path, "r") as f:
        user_data_template = f.read()

    # Substitute template variables
    user_data = user_data_template.replace("${config_content}", config_content)
    user_data = user_data.replace("${matrix_name}", matrix_name)
    user_data = user_data.replace("${unique_benchmark_name}", unique_benchmark_name)
    user_data = user_data.replace(
        "${s3_bucket_name}", terraform_outputs["s3_bucket_name"]
    )

    # Launch instance
    response = ec2.run_instances(
        LaunchTemplate={"LaunchTemplateId": terraform_outputs["launch_template_id"]},
        MinCount=1,
        MaxCount=1,
        UserData=user_data,
        TagSpecifications=[
            {
                "ResourceType": "instance",
                "Tags": [
                    {
                        "Key": "BenchmarkRun",
                        "Value": f"{matrix_name}_{unique_benchmark_name}",
                    },
                    {"Key": "Timestamp", "Value": unique_benchmark_name},
                ],
            }
        ],
    )

    instance_id = response["Instances"][0]["InstanceId"]
    print(f"Launched benchmark instance: {instance_id}")
    print(
        f"Results will be at: s3://{terraform_outputs['s3_bucket_name']}/benchmarks/{unique_benchmark_name}/"
    )

    return instance_id, unique_benchmark_name


def wait_for_completion(s3_bucket, unique_benchmark_name, instance_id):
    """Wait for benchmark completion by monitoring S3 completion marker and instance state"""
    s3 = boto3.client("s3", region_name="us-east-2")
    ec2 = boto3.client("ec2", region_name="us-east-2")

    completion_key = f"benchmarks/{unique_benchmark_name}/user-data.log"
    max_wait_time_seconds = 3600 * 10  # 10 hour max wait
    check_interval = 180  # Check every 180 seconds
    elapsed_time = 0

    print(
        f"Waiting for benchmark completion (max {max_wait_time_seconds // 60} minutes)..."
    )
    print(f"Monitoring S3 key: s3://{s3_bucket}/{completion_key}")
    print(f"Instance ID: {instance_id}")

    while elapsed_time < max_wait_time_seconds:
        # Check if completion marker exists in S3
        try:
            s3.head_object(Bucket=s3_bucket, Key=completion_key)
            print(
                f"✅ Benchmark completed! Found completion marker after {elapsed_time // 60}m {elapsed_time % 60}s"
            )
            return True
        except s3.exceptions.NoSuchKey:
            # Completion marker doesn't exist yet
            pass
        except Exception as e:
            print(f"Error checking S3: {e}")

        # Check instance state
        try:
            response = ec2.describe_instances(InstanceIds=[instance_id])
            instance_state = response["Reservations"][0]["Instances"][0]["State"][
                "Name"
            ]

            if instance_state == "terminated":
                print(
                    f"  Instance {instance_id} terminated after {elapsed_time // 60}m {elapsed_time % 60}s"
                )
                # Wait a bit more for S3 uploads to complete
                print("Waiting additional 30s for final S3 uploads...")
                time.sleep(30)
                return True
            elif instance_state in ["stopped", "stopping"]:
                print(
                    f"  Instance {instance_id} stopped after {elapsed_time // 60}m {elapsed_time % 60}s"
                )
                time.sleep(30)  # Wait for final uploads
                return True
            elif instance_state in ["shutting-down"]:
                print(f"  Instance {instance_id} is shutting down...")
            elif instance_state == "running":
                print(
                    f"  Instance still running... ({elapsed_time // 60}m {elapsed_time % 60}s elapsed)"
                )
            else:
                print(f"  Instance state: {instance_state}")

        except Exception as e:
            print(f"Error checking instance state: {e}")

        time.sleep(check_interval)
        elapsed_time += check_interval

    print(
        f"  Timeout after {max_wait_time_seconds // 60} minutes. Benchmark may still be running."
    )
    return False


def cleanup_benchmark_instances():
    """Terminate any running benchmark instances"""
    ec2 = boto3.client("ec2", region_name="us-east-2")

    # Find instances with our benchmark tags that are still running
    response = ec2.describe_instances(
        Filters=[
            {"Name": "tag:Purpose", "Values": ["yardbird-benchmarking"]},
            {"Name": "instance-state-name", "Values": ["running", "pending"]},
        ]
    )

    instance_ids = []
    for reservation in response["Reservations"]:
        for instance in reservation["Instances"]:
            instance_ids.append(instance["InstanceId"])
            print(f"Found running benchmark instance: {instance['InstanceId']}")

    if instance_ids:
        print(f"Terminating {len(instance_ids)} benchmark instances...")
        ec2.terminate_instances(InstanceIds=instance_ids)
        print("Benchmark instances terminated.")
    else:
        print("No running benchmark instances found.")


def destroy_infrastructure():
    """Destroy infrastructure using Terraform"""

    run_terraform_command(["destroy", "-auto-approve"], cwd=TERRAFORM_DIR)


def main():
    parser = argparse.ArgumentParser(
        description="Terraform-based benchmark orchestration"
    )
    subparsers = parser.add_subparsers(dest="command", help="Commands")

    # Run command
    run_parser = subparsers.add_parser("run", help="Run benchmarks")
    run_parser.add_argument("config", help="Benchmark configuration file")
    run_parser.add_argument("--matrix", required=True, help="Matrix name to run")
    run_parser.add_argument("--wait", action="store_true", help="Wait for completion")
    run_parser.add_argument("--download", help="Download results to directory")

    # Destroy command
    _ = subparsers.add_parser("destroy", help="Destroy infrastructure")

    args = parser.parse_args()

    if args.command == "run":
        # Get terraform outputs
        outputs_json = run_terraform_command(["output", "-json"], cwd=TERRAFORM_DIR)
        if not outputs_json:
            print("No terraform outputs found. Deploy infrastructure first.")
            return

        outputs = json.loads(outputs_json)
        terraform_outputs = {k: v["value"] for k, v in outputs.items()}

        instance_id, unique_benchmark_name = launch_benchmark_instance(
            args.config, args.matrix, terraform_outputs
        )

        if args.wait:
            wait_for_completion(
                terraform_outputs["s3_bucket_name"], unique_benchmark_name, instance_id
            )

            if args.download:
                download_dir = Path(args.download)
                print(f"Downloading results to {download_dir}")
                subprocess.run(
                    [
                        "aws",
                        "s3",
                        "sync",
                        f"s3://{terraform_outputs['s3_bucket_name']}/benchmarks/{unique_benchmark_name}",
                        str(download_dir),
                    ]
                )

    elif args.command == "destroy":
        destroy_infrastructure()
        print("Infrastructure destroyed successfully!")

    else:
        parser.print_help()


if __name__ == "__main__":
    main()
