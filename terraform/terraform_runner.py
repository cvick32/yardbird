#!/usr/bin/env python3

import subprocess
import json
import argparse
import time
import boto3
from pathlib import Path
from datetime import datetime


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
    terraform_dir = Path(__file__).parent

    # Initialize terraform
    run_terraform_command(["init"], cwd=terraform_dir)

    # Plan
    plan_cmd = ["plan"]
    if config_vars:
        for key, value in config_vars.items():
            plan_cmd.extend(["-var", f"{key}={value}"])

    run_terraform_command(plan_cmd, cwd=terraform_dir)

    # Apply
    apply_cmd = ["apply", "-auto-approve"]
    if config_vars:
        for key, value in config_vars.items():
            apply_cmd.extend(["-var", f"{key}={value}"])

    output = run_terraform_command(apply_cmd, cwd=terraform_dir)

    # Get outputs
    outputs_json = run_terraform_command(["output", "-json"], cwd=terraform_dir)
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
    terraform_dir = Path(__file__).parent
    user_data_template_path = terraform_dir / "user_data.sh"
    
    with open(user_data_template_path, 'r') as f:
        user_data_template = f.read()
    
    # Substitute template variables
    user_data = user_data_template.replace('${config_content}', config_content)
    user_data = user_data.replace('${matrix_name}', matrix_name)
    user_data = user_data.replace('${timestamp}', timestamp)
    user_data = user_data.replace('${s3_bucket_name}', terraform_outputs["s3_bucket_name"])

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


def destroy_infrastructure():
    """Destroy infrastructure using Terraform"""
    terraform_dir = Path(__file__).parent
    run_terraform_command(["destroy", "-auto-approve"], cwd=terraform_dir)


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
    destroy_parser = subparsers.add_parser("destroy", help="Destroy infrastructure")

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
        terraform_dir = Path(__file__).parent
        outputs_json = run_terraform_command(["output", "-json"], cwd=terraform_dir)
        if not outputs_json:
            print("No terraform outputs found. Deploy infrastructure first.")
            return

        outputs = json.loads(outputs_json)
        terraform_outputs = {k: v["value"] for k, v in outputs.items()}

        instance_id, timestamp = launch_benchmark_instance(
            args.config, args.matrix, terraform_outputs
        )

        if args.wait:
            print("Waiting for benchmark completion...")
            # Simple wait implementation
            time.sleep(60)  # Wait a minute before checking

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

    elif args.command == "destroy":
        destroy_infrastructure()
        print("Infrastructure destroyed successfully!")

    else:
        parser.print_help()


if __name__ == "__main__":
    main()
