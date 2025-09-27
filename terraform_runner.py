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


def deploy_infrastructure(config_vars=None):
    """Deploy infrastructure using Terraform"""

    # Initialize terraform
    run_terraform_command(["init"], cwd=TERRAFORM_DIR)

    # Plan
    plan_cmd = ["plan"]
    if config_vars:
        for key, value in config_vars.items():
            plan_cmd.extend(["-var", f"{key}={value}"])

    run_terraform_command(plan_cmd, cwd=TERRAFORM_DIR)

    # Apply
    apply_cmd = ["apply", "-auto-approve"]
    if config_vars:
        for key, value in config_vars.items():
            apply_cmd.extend(["-var", f"{key}={value}"])

    run_terraform_command(apply_cmd, cwd=TERRAFORM_DIR)

    # Get outputs
    outputs_json = run_terraform_command(["output", "-json"], cwd=TERRAFORM_DIR)
    if outputs_json:
        outputs = json.loads(outputs_json)
        return {k: v["value"] for k, v in outputs.items()}

    return {}


def launch_benchmark_instance(config_file, matrix_name, terraform_outputs):
    """Launch instance using deployed infrastructure"""

    # Read config
    with open(config_file) as f:
        config_content = f.read()

    ec2 = boto3.client("ec2", region_name="us-east-2")  # Use us-east-2 for key pairs

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    # Read user data template and substitute variables

    user_data_template_path = TERRAFORM_DIR / "user_data.sh"

    with open(user_data_template_path, "r") as f:
        user_data_template = f.read()

    # Substitute template variables
    user_data = user_data_template.replace("${config_content}", config_content)
    user_data = user_data.replace("${matrix_name}", matrix_name)
    user_data = user_data.replace("${timestamp}", timestamp)
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
                    {"Key": "BenchmarkRun", "Value": f"{matrix_name}_{timestamp}"},
                    {"Key": "Timestamp", "Value": timestamp},
                ],
            }
        ],
    )

    instance_id = response["Instances"][0]["InstanceId"]
    print(f"Launched benchmark instance: {instance_id}")
    print(
        f"Results will be at: s3://{terraform_outputs['s3_bucket_name']}/benchmarks/{timestamp}/"
    )

    return instance_id, timestamp


def wait_for_completion(s3_bucket, timestamp, instance_id):
    """Wait for benchmark completion by monitoring S3 completion marker and instance state"""
    s3 = boto3.client("s3", region_name="us-east-2")
    ec2 = boto3.client("ec2", region_name="us-east-2")

    completion_key = f"benchmarks/{timestamp}/user-data.log"
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

    # Deploy command
    deploy_parser = subparsers.add_parser("deploy", help="Deploy infrastructure")
    deploy_parser.add_argument("--s3-bucket", help="S3 bucket name")
    deploy_parser.add_argument(
        "--instance-type", default="c5.xlarge", help="EC2 instance type"
    )

    # Run command
    run_parser = subparsers.add_parser("run", help="Run benchmarks")
    run_parser.add_argument("config", help="Benchmark configuration file")
    run_parser.add_argument("--matrix", required=True, help="Matrix name to run")
    run_parser.add_argument("--wait", action="store_true", help="Wait for completion")
    run_parser.add_argument("--download", help="Download results to directory")

    # Destroy command
    _ = subparsers.add_parser("destroy", help="Destroy infrastructure")

    args = parser.parse_args()

    if args.command == "deploy":
        config_vars = {}
        if args.s3_bucket:
            config_vars["s3_bucket_name"] = args.s3_bucket
        if args.instance_type:
            config_vars["instance_type"] = args.instance_type

        outputs = deploy_infrastructure(config_vars)
        print("Infrastructure deployed successfully!")
        print("Outputs:", json.dumps(outputs, indent=2))

    elif args.command == "run":
        # Get terraform outputs
        outputs_json = run_terraform_command(["output", "-json"], cwd=TERRAFORM_DIR)
        if not outputs_json:
            print("No terraform outputs found. Deploy infrastructure first.")
            return

        outputs = json.loads(outputs_json)
        terraform_outputs = {k: v["value"] for k, v in outputs.items()}

        instance_id, timestamp = launch_benchmark_instance(
            args.config, args.matrix, terraform_outputs
        )

        if args.wait:
            wait_for_completion(
                terraform_outputs["s3_bucket_name"], timestamp, instance_id
            )

            if args.download:
                download_dir = Path(args.download)
                print(f"Downloading results to {download_dir}")
                subprocess.run(
                    [
                        "aws",
                        "s3",
                        "sync",
                        f"s3://{terraform_outputs['s3_bucket_name']}/benchmarks/{timestamp}",
                        str(download_dir),
                    ]
                )
        cleanup_benchmark_instances()

    elif args.command == "destroy":
        destroy_infrastructure()
        print("Infrastructure destroyed successfully!")

    else:
        parser.print_help()


if __name__ == "__main__":
    main()
