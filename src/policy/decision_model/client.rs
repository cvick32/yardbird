use serde_json::Value;
use std::time::Duration;

pub(super) trait DecisionClient {
    fn decide(&mut self, request: &Value) -> anyhow::Result<Value>;
}

pub(super) struct JevClient {
    timeout: Duration,
}

impl JevClient {
    pub fn new(timeout_secs: u64) -> Self {
        Self {
            timeout: Duration::from_secs(timeout_secs),
        }
    }
}

impl DecisionClient for JevClient {
    fn decide(&mut self, request: &Value) -> anyhow::Result<Value> {
        let key = std::env::var("JEV_API_KEY")
            .map_err(|_| anyhow::anyhow!("JEV_API_KEY is not configured"))?;
        anyhow::ensure!(!key.trim().is_empty(), "JEV_API_KEY is empty");
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()?;
        runtime.block_on(async {
            let client = reqwest::Client::builder()
                .timeout(self.timeout)
                .redirect(reqwest::redirect::Policy::none())
                .build()?;
            let mut response = client
                .post("https://api.typesafe.ai/v1/systemone")
                .bearer_auth(key)
                .json(request)
                .send()
                .await?
                .error_for_status()?;
            let mut body = Vec::new();
            while let Some(chunk) = response.chunk().await? {
                anyhow::ensure!(
                    body.len() + chunk.len() <= 4 * 1024 * 1024,
                    "Jev response exceeds 4 MiB"
                );
                body.extend_from_slice(&chunk);
            }
            Ok(serde_json::from_slice(&body)?)
        })
    }
}
