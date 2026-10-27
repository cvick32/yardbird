# UT account parameter references only; API key values stay in SSM.
# Use with UT AWS credentials, workspace ut, and -var-file=ut.tfvars.
aws_region = "us-east-2"

api_key_parameter_arns = [
  "arn:aws:ssm:us-east-2:913051689250:parameter/yardbird/jev-api-key",
  "arn:aws:ssm:us-east-2:913051689250:parameter/yardbird/openai-api-key",
]
