use super::{LlmOptions, LlmProvider};
use serde_json::Value;
use std::time::Duration;

pub(crate) trait LlmClient {
    fn infer(&mut self, request: &Value) -> anyhow::Result<Value>;
}

pub(crate) struct HttpClient {
    options: LlmOptions,
    timeout: Duration,
}

impl HttpClient {
    pub fn new(options: &LlmOptions) -> Self {
        Self {
            options: options.clone(),
            timeout: Duration::from_secs(options.llm_timeout_secs),
        }
    }

    pub(crate) fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = self.timeout.min(timeout);
        self
    }
}

impl LlmClient for HttpClient {
    fn infer(&mut self, request: &Value) -> anyhow::Result<Value> {
        let name = self.options.llm_provider.key_env();
        let key = std::env::var(name).map_err(|_| anyhow::anyhow!("{name} is not configured"))?;
        anyhow::ensure!(!key.trim().is_empty(), "{name} is empty");
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()?;
        runtime.block_on(async {
            let client = reqwest::Client::builder()
                .timeout(self.timeout)
                .redirect(reqwest::redirect::Policy::none())
                .retry(reqwest::retry::never())
                .build()?;
            let request = client.post(self.options.endpoint()?).json(request);
            let request = match self.options.llm_provider {
                LlmProvider::Openai | LlmProvider::Bedrock => request.bearer_auth(&key),
                LlmProvider::Anthropic => request
                    .header("x-api-key", &key)
                    .header("anthropic-version", "2023-06-01"),
            };
            // No automatic transport or semantic retries: each inference call
            // must appear in the experiment log and count against its budget.
            let mut response = request.send().await?;
            let status = response.status();
            let mut body = Vec::new();
            while let Some(chunk) = response.chunk().await? {
                anyhow::ensure!(
                    body.len() + chunk.len() <= 4 * 1024 * 1024,
                    "LLM response exceeds 4 MiB"
                );
                body.extend_from_slice(&chunk);
            }
            if !status.is_success() {
                // Keep provider diagnostics useful (unsupported model/schema,
                // rate limits, etc.) without copying an echoed credential.
                let value = serde_json::from_slice::<Value>(&body).unwrap_or(Value::Null);
                let message = value["error"]["message"]
                    .as_str()
                    .or_else(|| value["message"].as_str())
                    .unwrap_or("no JSON error message");
                let message = message
                    .replace(&key, "[REDACTED]")
                    .chars()
                    .take(2048)
                    .collect::<String>();
                anyhow::bail!("LLM HTTP status {status}: {message}");
            }
            Ok(serde_json::from_slice(&body)?)
        })
    }
}
