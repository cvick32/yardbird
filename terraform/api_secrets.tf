# Secret values are provisioned outside Terraform and never enter its state.
variable "api_key_parameter_arns" {
  description = "Exact SSM SecureString parameter ARNs readable by benchmark workers."
  type        = list(string)
  default     = []
}

variable "api_key_kms_key_arns" {
  description = "Optional customer-managed KMS keys used by these parameters."
  type        = list(string)
  default     = []
}

resource "aws_iam_role_policy" "benchmark_api_parameters" {
  count = length(var.api_key_parameter_arns) > 0 ? 1 : 0
  name  = "YardbirdBenchmarkAPIParameters"
  role  = aws_iam_role.benchmark_role.id
  policy = jsonencode({
    Version = "2012-10-17"
    Statement = concat([{
      Effect   = "Allow"
      Action   = ["ssm:GetParameter"]
      Resource = var.api_key_parameter_arns
      }], length(var.api_key_kms_key_arns) > 0 ? [{
      Effect   = "Allow"
      Action   = ["kms:Decrypt"]
      Resource = var.api_key_kms_key_arns
      Condition = {
        StringEquals = {
          "kms:ViaService" = "ssm.${var.aws_region}.amazonaws.com"
        }
      }
    }] : [])
  })
}
