//! Portable per-benchmark accounting. JSONL remains the per-call audit trail.
use serde::Serialize;
use serde_json::Value;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
};

#[derive(Debug, Default, Serialize)]
pub(crate) struct ApiUsage {
    schema_version: u32,
    currency: &'static str,
    status: &'static str,
    pub api_calls: usize,
    pub unknown_cost_calls: usize,
    pub unresolved_requests: usize,
    pub estimated_subtotal_usd: f64,
    pub estimated_total_usd: Option<f64>,
    api_seconds: f64,
    input_tokens: u64,
    output_tokens: u64,
    cached_input_tokens: u64,
    uncached_input_tokens: u64,
    short_cache_write_tokens: u64,
    long_cache_write_tokens: u64,
    token_usage_incomplete_calls: usize,
    episodes: usize,
    accepted_episodes: usize,
    /// Episodes handing off to ordinary search, not a count of installed lemmas.
    fallback_episodes: usize,
    pub dry_run: bool,
    resolved_models: BTreeSet<String>,
    log_available: bool,
    /// Accounting errors must not discard the verification result.
    evidence_error: Option<String>,
}

#[derive(Default)]
struct Accounting {
    summary: ApiUsage,
    requests: BTreeSet<u64>,
    skipped: BTreeSet<u64>,
    calls: BTreeMap<u64, Value>,
}

fn tokens_for(call: &Value) -> Value {
    let cost = &call["cost"];
    if cost["tokens"].is_object() {
        return cost["tokens"].clone();
    }
    if cost.get("input_tokens").is_some() {
        return cost.clone(); // JEV's configured-rate accounting.
    }
    // Usage is still useful when pricing is unavailable for a model/tier.
    let u = &call["usage"];
    let input = u["input_tokens"].as_u64();
    let output = u["output_tokens"].as_u64();
    let anthropic = call["configuration"]["llm_provider"] == "anthropic";
    let (read, write, short, long) = if anthropic {
        let write = u["cache_creation_input_tokens"]
            .as_u64()
            .unwrap_or_default();
        let long = u["cache_creation"]["ephemeral_1h_input_tokens"]
            .as_u64()
            .unwrap_or_default();
        (
            u["cache_read_input_tokens"].as_u64().unwrap_or_default(),
            write,
            write.saturating_sub(long),
            long,
        )
    } else {
        let d = &u["input_tokens_details"];
        let write = d["cache_write_tokens"].as_u64().unwrap_or_default();
        let long = d["cache_write_tokens_details"]["ttl_12h_tokens"]
            .as_u64()
            .unwrap_or_default();
        (
            d["cached_tokens"].as_u64().unwrap_or_default(),
            write,
            write.saturating_sub(long),
            long,
        )
    };
    let total = if anthropic {
        input.and_then(|n| n.checked_add(read)?.checked_add(write))
    } else {
        input
    };
    let uncached = if anthropic {
        input
    } else {
        input.and_then(|n| n.checked_sub(read)?.checked_sub(write))
    };
    serde_json::json!({"input_tokens":total, "output_tokens":output,
        "cached_input_tokens":read, "uncached_input_tokens":uncached,
        "short_cache_write_tokens":short, "long_cache_write_tokens":long})
}

impl Accounting {
    fn observe(&mut self, event: Value) {
        match event["event"].as_str() {
            Some("request") => {
                if let Some(id) = event["query_id"].as_u64() {
                    self.requests.insert(id);
                }
            }
            Some("request_skipped") => {
                if let Some(id) = event["query_id"].as_u64() {
                    self.skipped.insert(id);
                }
                self.summary.dry_run |= event["outcome"] == "dry_run";
            }
            Some("episode_end") => {
                self.summary.episodes += 1;
                self.summary.accepted_episodes += usize::from(event["outcome"] == "violated");
                self.summary.fallback_episodes += usize::from(event["ordinary_fallback"] == true);
            }
            _ => {}
        }
        // Conditional JEV emits a synthetic attempt_result with cost:null after
        // individually billed binding_result records. It is not another call.
        if event["cost"].is_object() {
            if let Some(id) = event["query_id"].as_u64() {
                if self.calls.insert(id, event).is_some() {
                    self.summary.evidence_error = Some("duplicate per-call cost record".into());
                }
            } else {
                self.summary.evidence_error = Some("cost record missing query_id".into());
            }
        }
    }

    fn finish(mut self) -> ApiUsage {
        let s = &mut self.summary;
        s.schema_version = 1;
        s.currency = "USD";
        s.unresolved_requests = self
            .requests
            .iter()
            .filter(|id| !self.calls.contains_key(id) && !self.skipped.contains(id))
            .count();
        s.api_calls = self.calls.len() + s.unresolved_requests;
        s.unknown_cost_calls = s.unresolved_requests;
        s.token_usage_incomplete_calls = s.unresolved_requests;
        for call in self.calls.values() {
            match call["cost"]["estimated_usd"]
                .as_f64()
                .filter(|c| c.is_finite() && *c >= 0.0)
            {
                Some(cost) if (s.estimated_subtotal_usd + cost).is_finite() => {
                    s.estimated_subtotal_usd += cost
                }
                _ => s.unknown_cost_calls += 1,
            }
            s.api_seconds += call["elapsed_secs"].as_f64().unwrap_or_default();
            let tokens = tokens_for(call);
            s.token_usage_incomplete_calls += usize::from(
                tokens["input_tokens"].as_u64().is_none()
                    || tokens["output_tokens"].as_u64().is_none(),
            );
            s.input_tokens += tokens["input_tokens"].as_u64().unwrap_or_default();
            s.output_tokens += tokens["output_tokens"].as_u64().unwrap_or_default();
            s.cached_input_tokens += tokens["cached_input_tokens"].as_u64().unwrap_or_default();
            s.uncached_input_tokens += tokens["uncached_input_tokens"].as_u64().unwrap_or_default();
            s.short_cache_write_tokens += tokens["short_cache_write_tokens"]
                .as_u64()
                .unwrap_or_default();
            s.long_cache_write_tokens += tokens["long_cache_write_tokens"]
                .as_u64()
                .unwrap_or_default();
            if let Some(model) = call["resolved_model"]
                .as_str()
                .or_else(|| call["response"]["model"].as_str())
            {
                s.resolved_models.insert(model.to_owned());
            }
        }
        s.estimated_total_usd = (s.unknown_cost_calls == 0 && s.evidence_error.is_none())
            .then_some(s.estimated_subtotal_usd);
        s.status = if s.estimated_total_usd.is_some() {
            "estimated"
        } else {
            "incomplete"
        };
        self.summary
    }
}

/// Called after the subprocess exits or is killed. A final partial line or
/// unanswered request preserves a lower-bound subtotal and an unknown total.
pub(crate) fn summarize(path: Option<&Path>) -> ApiUsage {
    let mut accounting = Accounting::default();
    let Some(path) = path else {
        return accounting.finish();
    };
    let file = match File::open(path) {
        Ok(file) => file,
        Err(error) => {
            accounting.summary.evidence_error = Some(format!("API log unavailable: {error}"));
            return accounting.finish();
        }
    };
    accounting.summary.log_available = true;
    for line in BufReader::new(file).lines() {
        match line {
            Ok(line) => match serde_json::from_str(&line) {
                Ok(event) => accounting.observe(event),
                Err(_) => {
                    accounting.summary.evidence_error =
                        Some("incomplete or invalid JSONL record".into())
                }
            },
            Err(error) => {
                accounting.summary.evidence_error = Some(format!("API log read failed: {error}"));
                break;
            }
        }
    }
    accounting.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn jev_staged_and_conditional_calls_are_counted_once() {
        let mut a = Accounting::default();
        for (id, event) in [
            (1, "axiom_result"),
            (2, "binding_result"),
            (3, "binding_result"),
        ] {
            a.observe(json!({"event":"request","query_id":id}));
            a.observe(json!({"event":event,"query_id":id,"cost":{"estimated_usd":0.01,"input_tokens":100,"output_tokens":10},"elapsed_secs":0.2,"response":{"model":"jev-resolved"}}));
        }
        a.observe(json!({"event":"attempt_result","query_id":3,"cost":null}));
        a.observe(
            json!({"event":"episode_end","outcome":"attempts_exhausted","ordinary_fallback":true}),
        );
        let s = a.finish();
        assert_eq!(s.api_calls, 3);
        assert_eq!(s.estimated_total_usd, Some(0.03));
        assert_eq!(s.input_tokens, 300);
        assert_eq!(s.fallback_episodes, 1);
    }

    #[test]
    fn llm_totals_do_not_sum_repeated_cumulative_fields() {
        let mut a = Accounting::default();
        for id in 1..=2 {
            a.observe(
                json!({"event":"response","query_id":id,"cost":{"estimated_usd":0.1,
                "tokens":{"input_tokens":100,"cached_input_tokens":80,"output_tokens":20}},
                "run_cost":{"estimated_total_usd":99},"resolved_model":"astra"}),
            );
        }
        a.observe(json!({"event":"episode_end","outcome":"violated","run_cost":{"estimated_total_usd":99}}));
        let s = a.finish();
        assert_eq!(s.estimated_total_usd, Some(0.2));
        assert_eq!(s.cached_input_tokens, 160);
        assert_eq!(s.accepted_episodes, 1);
        assert_eq!(s.resolved_models.len(), 1);
    }

    #[test]
    fn skipped_and_unanswered_requests_and_transport_failures_are_distinct() {
        let mut a = Accounting::default();
        for id in 1..=3 {
            a.observe(json!({"event":"request","query_id":id}));
        }
        a.observe(json!({"event":"request_skipped","query_id":1,"outcome":"dry_run"}));
        a.observe(json!({"event":"transport_error","query_id":2,"cost":{"estimated_usd":null}}));
        let s = a.finish();
        assert_eq!(s.api_calls, 2);
        assert_eq!(s.unknown_cost_calls, 2);
        assert_eq!(s.unresolved_requests, 1);
        assert!(s.estimated_total_usd.is_none());
        assert!(s.dry_run);
    }

    #[test]
    fn missing_and_truncated_logs_do_not_destroy_known_subtotals() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("api.jsonl");
        assert!(summarize(Some(&path)).estimated_total_usd.is_none());
        std::fs::write(
            &path,
            "{\"event\":\"response\",\"query_id\":1,\"cost\":{\"estimated_usd\":0.5}}\n{\"event\":",
        )
        .unwrap();
        let s = summarize(Some(&path));
        assert_eq!(s.estimated_subtotal_usd, 0.5);
        assert!(s.estimated_total_usd.is_none());
        assert_eq!(summarize(None).estimated_total_usd, Some(0.0));
    }
    #[test]
    fn usage_survives_unavailable_pricing_for_both_llm_providers() {
        for provider in ["openai", "anthropic"] {
            let mut a = Accounting::default();
            a.observe(json!({"event":"response", "query_id":1,
            "configuration":{"llm_provider":provider},
            "cost":{"estimated_usd":null}, "usage":{
                "input_tokens":100, "output_tokens":20,
                "input_tokens_details":{"cached_tokens":30},
                "cache_read_input_tokens":30, "cache_creation_input_tokens":10
            }}));
            let s = a.finish();
            assert!(s.estimated_total_usd.is_none());
            assert_eq!(s.input_tokens, if provider == "openai" { 100 } else { 140 });
            assert_eq!(s.cached_input_tokens, 30);
            assert_eq!(s.output_tokens, 20);
        }
    }
}
