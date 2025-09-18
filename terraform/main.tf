terraform {
  required_providers {
    aws = {
      source  = "hashicorp/aws"
      version = "~> 5.0"
    }
    random = {
      source  = "hashicorp/random"
      version = "~> 3.1"
    }
  }
}

provider "aws" {
  region = var.aws_region
}

# Variables
variable "aws_region" {
  description = "AWS region"
  type        = string
  default     = "us-east-2"
}

variable "instance_type" {
  description = "EC2 instance type"
  type        = string
  default     = "c5.xlarge"
}

variable "s3_bucket_name" {
  description = "S3 bucket for benchmark results"
  type        = string
  default     = "yardbird-benchmarks"
}

variable "key_pair_name" {
  description = "EC2 key pair name"
  type        = string
  default     = "yardbird-benchmark-key"
}

resource "random_id" "bucket_suffix" {
  byte_length = 4
}

# S3 bucket for results
resource "aws_s3_bucket" "benchmark_results" {
  bucket = "${var.s3_bucket_name}-${random_id.bucket_suffix.hex}"
}

resource "aws_s3_bucket_versioning" "benchmark_results" {
  bucket = aws_s3_bucket.benchmark_results.id
  versioning_configuration {
    status = "Enabled"
  }
}

resource "aws_s3_bucket_lifecycle_configuration" "benchmark_results" {
  bucket = aws_s3_bucket.benchmark_results.id

  rule {
    id     = "cleanup_old_benchmarks"
    status = "Enabled"

    filter {
      prefix = ""
    }

    expiration {
      days = 90
    }

    noncurrent_version_expiration {
      noncurrent_days = 30
    }
  }
}

# IAM role for EC2 instances
resource "aws_iam_role" "benchmark_role" {
  name = "YardbirdBenchmarkRole"

  assume_role_policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Action = "sts:AssumeRole"
        Effect = "Allow"
        Principal = {
          Service = "ec2.amazonaws.com"
        }
      }
    ]
  })
}

# IAM policy for EC2 management permissions
resource "aws_iam_role_policy" "benchmark_ec2_policy" {
  name = "YardbirdBenchmarkEC2Policy"
  role = aws_iam_role.benchmark_role.id

  policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Effect = "Allow"
        Action = [
          "ec2:DescribeImages",
          "ec2:DescribeInstances",
          "ec2:DescribeInstanceTypes"
        ]
        Resource = "*"
      }
    ]
  })
}

resource "aws_iam_role_policy" "benchmark_s3_policy" {
  name = "YardbirdBenchmarkS3Policy"
  role = aws_iam_role.benchmark_role.id

  policy = jsonencode({
    Version = "2012-10-17"
    Statement = [
      {
        Effect = "Allow"
        Action = [
          "s3:GetObject",
          "s3:PutObject",
          "s3:DeleteObject",
          "s3:ListBucket"
        ]
        Resource = [
          aws_s3_bucket.benchmark_results.arn,
          "${aws_s3_bucket.benchmark_results.arn}/*"
        ]
      }
    ]
  })
}

resource "aws_iam_instance_profile" "benchmark_profile" {
  name = "YardbirdBenchmarkRole"
  role = aws_iam_role.benchmark_role.name
}

# Security group for benchmark instances
resource "aws_security_group" "benchmark_sg" {
  name_prefix = "yardbird-benchmark-"
  description = "Security group for Yardbird benchmark instances"

  # Only allow outbound traffic
  egress {
    from_port   = 0
    to_port     = 0
    protocol    = "-1"
    cidr_blocks = ["0.0.0.0/0"]
  }

  tags = {
    Name = "yardbird-benchmark-sg"
  }
}

# Launch template for benchmark instances
resource "aws_launch_template" "benchmark_template" {
  name_prefix   = "yardbird-benchmark-"
  image_id      = "ami-0e83be366243f524a"  # Ubuntu 22.04 LTS us-east-2
  instance_type = var.instance_type
  key_name      = var.key_pair_name

  vpc_security_group_ids = [aws_security_group.benchmark_sg.id]

  iam_instance_profile {
    name = aws_iam_instance_profile.benchmark_profile.name
  }

  tag_specifications {
    resource_type = "instance"
    tags = {
      Name    = "yardbird-benchmark"
      Purpose = "yardbird-benchmarking"
      AutoTerminate = "true"
    }
  }
}

# Using hardcoded Ubuntu 22.04 LTS AMI for us-east-2 to avoid permission issues
# ami-0c2d3e23f757b5d84 is Ubuntu 22.04 LTS

# Outputs
output "s3_bucket_name" {
  value = aws_s3_bucket.benchmark_results.bucket
}

output "launch_template_id" {
  value = aws_launch_template.benchmark_template.id
}

output "iam_instance_profile_name" {
  value = aws_iam_instance_profile.benchmark_profile.name
}

output "security_group_id" {
  value = aws_security_group.benchmark_sg.id
}