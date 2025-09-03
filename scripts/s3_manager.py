#!/usr/bin/env python3

import subprocess
import boto3
import argparse
import json
from datetime import datetime
from pathlib import Path


def upload_results(local_file, s3_bucket, prefix=None):
    """Upload benchmark results to S3"""
    s3 = boto3.client("s3")

    if prefix is None:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        prefix = f"benchmarks/{timestamp}"

    local_path = Path(local_file)
    s3_key = f"{prefix}/{local_path.name}"

    print(f"Uploading {local_file} to s3://{s3_bucket}/{s3_key}")
    s3.upload_file(str(local_file), s3_bucket, s3_key)

    return f"s3://{s3_bucket}/{s3_key}"


def download_results(s3_bucket, s3_key, local_file):
    """Download results from S3"""
    s3 = boto3.client("s3")

    print(f"Downloading s3://{s3_bucket}/{s3_key} to {local_file}")
    s3.download_file(s3_bucket, s3_key, str(local_file))


def list_results(s3_bucket, prefix="benchmarks/"):
    """List available benchmark results"""
    s3 = boto3.client("s3")

    response = s3.list_objects_v2(Bucket=s3_bucket, Prefix=prefix)

    if "Contents" not in response:
        print("No results found")
        return []

    results = []
    for obj in response["Contents"]:
        if obj["Key"].endswith(".json"):
            results.append(
                {
                    "key": obj["Key"],
                    "size": obj["Size"],
                    "modified": obj["LastModified"].isoformat(),
                }
            )

    return results


def sync_directory(local_dir, s3_bucket, s3_prefix, upload=True):
    """Sync directory with S3"""
    if upload:
        cmd = ["aws", "s3", "sync", str(local_dir), f"s3://{s3_bucket}/{s3_prefix}"]
    else:
        cmd = ["aws", "s3", "sync", f"s3://{s3_bucket}/{s3_prefix}", str(local_dir)]

    print(f"Running: {' '.join(cmd)}")
    result = subprocess.run(cmd, check=True)


def main():
    parser = argparse.ArgumentParser(description="S3 Results Manager")
    subparsers = parser.add_subparsers(dest="command", help="Commands")

    # Upload command
    upload_parser = subparsers.add_parser("upload", help="Upload results")
    upload_parser.add_argument("file", help="Local file to upload")
    upload_parser.add_argument("bucket", help="S3 bucket")
    upload_parser.add_argument("--prefix", help="S3 prefix")

    # Download command
    download_parser = subparsers.add_parser("download", help="Download results")
    download_parser.add_argument("bucket", help="S3 bucket")
    download_parser.add_argument("key", help="S3 key")
    download_parser.add_argument("file", help="Local file")

    # List command
    list_parser = subparsers.add_parser("list", help="List results")
    list_parser.add_argument("bucket", help="S3 bucket")
    list_parser.add_argument("--prefix", default="benchmarks/", help="S3 prefix")

    # Sync command
    sync_parser = subparsers.add_parser("sync", help="Sync directory")
    sync_parser.add_argument("bucket", help="S3 bucket")
    sync_parser.add_argument("prefix", help="S3 prefix")
    sync_parser.add_argument("local_dir", help="Local directory")
    sync_parser.add_argument(
        "--download", action="store_true", help="Download instead of upload"
    )

    args = parser.parse_args()

    if args.command == "upload":
        url = upload_results(args.file, args.bucket, args.prefix)
        print(f"Uploaded to: {url}")

    elif args.command == "download":
        download_results(args.bucket, args.key, args.file)

    elif args.command == "list":
        results = list_results(args.bucket, args.prefix)
        print(f"Found {len(results)} results:")
        for result in results:
            print(f"  {result['key']} ({result['size']} bytes, {result['modified']})")

    elif args.command == "sync":
        sync_directory(
            args.local_dir, args.bucket, args.prefix, upload=not args.download
        )

    else:
        parser.print_help()


if __name__ == "__main__":
    main()
