use anyhow::Result;
use reqwest::Client;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AnalysisType {
    #[serde(rename = "PROPOSE_INVARIANT")]
    ProposeInvariant,
    #[serde(rename = "ANALYZE_COUNTEREXAMPLE")]
    AnalyzeCounterexample,
    #[serde(rename = "SUGGEST_LEMMAS")]
    SuggestLemmas,
    #[serde(rename = "DEBUG_STRATEGY")]
    DebugStrategy,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationContext {
    pub variables: Vec<String>,
    pub init_conditions: String,
    pub trans_conditions: String,
    pub property: String,
    pub array_operations: Vec<String>,
    pub loop_bounds: Vec<String>,
    pub hints: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationRequest {
    pub analysis_type: AnalysisType,
    pub context: VerificationContext,
    pub failed_invariants: Vec<String>,
    pub counterexample: Option<String>,
    pub current_strategy: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InvariantCandidate {
    pub formula: String,
    pub confidence: i32,
    pub reasoning: String,
    pub referenced_vars: Vec<String>,
    pub invariant_type: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InvariantSuggestions {
    pub candidates: Vec<InvariantCandidate>,
    pub analysis: String,
    pub strategy_hints: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct BamlRequest {
    request: VerificationRequest,
}

pub struct BamlClient {
    client: Client,
    base_url: String,
}

impl BamlClient {
    pub fn new(base_url: Option<String>) -> Self {
        let base_url = base_url.unwrap_or_else(|| "http://localhost:2024".to_string());
        Self {
            client: Client::new(),
            base_url,
        }
    }

    pub async fn propose_invariant(
        &self,
        request: VerificationRequest,
    ) -> Result<InvariantSuggestions> {
        let url = format!("{}/call/ProposeInvariant", self.base_url);
        let body = BamlRequest { request };

        let response = self.client.post(&url).json(&body).send().await?;

        if response.status().is_success() {
            let suggestions: InvariantSuggestions = response.json().await?;
            Ok(suggestions)
        } else {
            anyhow::bail!("BAML request failed with status: {}", response.status())
        }
    }

    pub async fn analyze_counterexample(
        &self,
        request: VerificationRequest,
    ) -> Result<InvariantSuggestions> {
        let url = format!("{}/call/AnalyzeCounterexample", self.base_url);
        let body = BamlRequest { request };

        let response = self.client.post(&url).json(&body).send().await?;

        if response.status().is_success() {
            let suggestions: InvariantSuggestions = response.json().await?;
            Ok(suggestions)
        } else {
            anyhow::bail!("BAML request failed with status: {}", response.status())
        }
    }

    pub async fn suggest_lemmas(
        &self,
        request: VerificationRequest,
    ) -> Result<InvariantSuggestions> {
        let url = format!("{}/call/SuggestLemmas", self.base_url);
        let body = BamlRequest { request };

        let response = self.client.post(&url).json(&body).send().await?;

        if response.status().is_success() {
            let suggestions: InvariantSuggestions = response.json().await?;
            Ok(suggestions)
        } else {
            anyhow::bail!("BAML request failed with status: {}", response.status())
        }
    }
}

/// Helper function to extract context from a VMT problem
pub fn extract_verification_context(
    vmt_content: &str,
    variables: Vec<String>,
    array_ops: Vec<String>,
) -> VerificationContext {
    // Parse VMT content to extract relevant sections
    let mut init_conditions = String::new();
    let mut trans_conditions = String::new();
    let mut property = String::new();

    for line in vmt_content.lines() {
        let line = line.trim();
        if line.contains(":init true") {
            // Extract init conditions (simplified parsing)
            if let Some(start) = line.find("(and") {
                if let Some(end) = line.rfind(")") {
                    init_conditions = line[start..end + 1].to_string();
                }
            }
        } else if line.contains(":trans true") {
            // Extract transition conditions
            if let Some(start) = line.find("(and") {
                if let Some(end) = line.rfind(")") {
                    trans_conditions = line[start..end + 1].to_string();
                }
            }
        } else if line.contains(":invar-property") {
            // Extract property
            if let Some(start) = line.find("(and") {
                if let Some(end) = line.rfind(")") {
                    property = line[start..end + 1].to_string();
                }
            }
        }
    }

    VerificationContext {
        variables,
        init_conditions,
        trans_conditions,
        property,
        array_operations: array_ops,
        loop_bounds: vec![], // Would need more sophisticated parsing
        hints: vec![],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verification_context_creation() {
        let context = VerificationContext {
            variables: vec![
                "i".to_string(),
                "n".to_string(),
                "a".to_string(),
                "b".to_string(),
            ],
            init_conditions: "(= i 0)".to_string(),
            trans_conditions:
                "(and (= (store b i (select a i)) b_next) (< i n) (= (+ i 1) i_next))".to_string(),
            property: "(=> (>= i n) (= (select a Z) (select b Z)))".to_string(),
            array_operations: vec!["select".to_string(), "store".to_string()],
            loop_bounds: vec!["(< i n)".to_string()],
            hints: vec![],
        };

        assert_eq!(context.variables.len(), 4);
        assert!(context.init_conditions.contains("i 0"));
    }
}
