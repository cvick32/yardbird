use super::*;

fn options(provider: LlmProvider) -> LlmOptions {
    LlmOptions {
        llm_provider: provider,
        llm_model: Some(
            match provider {
                LlmProvider::Openai => "gpt-6-astra",
                LlmProvider::Anthropic => "claude-sonnet-5-5",
            }
            .into(),
        ),
        ..Default::default()
    }
}

fn openai(input: u64) -> Value {
    json!({"usage":{"input_tokens":input,"input_tokens_details":{"cached_tokens":0},
        "output_tokens":2000,"output_tokens_details":{"reasoning_tokens":1500}}})
}

fn close(value: &Value, expected: f64) {
    assert!(
        (value.as_f64().unwrap() - expected).abs() < 1e-10,
        "{value} != {expected}"
    );
}

#[test]
fn openai_disjoint_cache_categories_and_reasoning_are_charged_once() {
    let mut response = openai(20_000);
    response["usage"]["input_tokens_details"] = json!({"cached_tokens":5000,
        "cache_write_tokens":3000,"cache_write_tokens_details":{"ttl_30m_tokens":2000,"ttl_12h_tokens":1000}});
    let cost = estimate(&options(LlmProvider::Openai), &response);
    assert_eq!(cost["tokens"]["uncached_input_tokens"], 12000);
    close(&cost["estimated_usd"], 0.12 + 0.005 + 0.025 + 0.025 + 0.1);
    close(&cost["components_usd"]["output"], 0.1);
}

#[test]
fn anthropic_input_excludes_cache_and_supports_both_write_lifetimes() {
    let response = json!({"usage":{"input_tokens":12000,"output_tokens":2000,
        "cache_read_input_tokens":5000,"cache_creation_input_tokens":3000,
        "cache_creation":{"ephemeral_5m_input_tokens":2000,"ephemeral_1h_input_tokens":1000}}});
    let cost = estimate(&options(LlmProvider::Anthropic), &response);
    assert_eq!(cost["tokens"]["input_tokens"], 20000);
    close(
        &cost["estimated_usd"],
        0.024 + 0.0005 + 0.005 + 0.004 + 0.02,
    );
    let mut old = response;
    old["usage"]
        .as_object_mut()
        .unwrap()
        .remove("cache_creation");
    close(
        &estimate(&options(LlmProvider::Anthropic), &old)["components_usd"]["short_cache_write"],
        0.0075,
    );
}

#[test]
fn astra_long_context_threshold_applies_to_whole_request() {
    let options = options(LlmProvider::Openai);
    close(
        &estimate(&options, &openai(272_000))["estimated_usd"],
        2.72 + 0.1,
    );
    close(
        &estimate(&options, &openai(272_001))["estimated_usd"],
        5.44002 + 0.15,
    );
    let mut cached = openai(272_001);
    cached["usage"]["input_tokens_details"]["cached_tokens"] = json!(272001);
    close(
        &estimate(&options, &cached)["estimated_usd"],
        0.544002 + 0.15,
    );
}

#[test]
fn unknown_models_tiers_usage_and_inconsistent_cache_are_not_free() {
    let options = options(LlmProvider::Openai);
    let base = openai(100);
    let mut cases = vec![
        json!({}),
        base.clone(),
        base.clone(),
        base.clone(),
        base.clone(),
        base.clone(),
        base.clone(),
    ];
    cases[1]["model"] = json!("unknown-resolved-model");
    cases[2]["service_tier"] = json!("priority");
    cases[3]["usage"]["input_tokens_details"]["cached_tokens"] = json!(101);
    cases[4]["usage"]["output_tokens"] = json!(-1);
    cases[5]["usage"]["input_tokens_details"] = json!({"cached_tokens":0,"cache_write_tokens":10,
        "cache_write_tokens_details":{"ttl_30m_tokens":9,"ttl_12h_tokens":0}});
    cases[6]["usage"]["inference_geo"] = json!("us");
    for response in cases {
        let cost = estimate(&options, &response);
        assert_eq!(cost["status"], "unknown", "{cost}");
        assert!(cost["estimated_usd"].is_null());
        assert!(cost["reason"].is_string());
    }
}

#[test]
fn custom_effective_rates_replace_presets_and_require_nonzero_categories() {
    let mut options = options(LlmProvider::Openai);
    options.pricing = LlmPricing {
        llm_input_usd_per_million: Some(2.0),
        llm_output_usd_per_million: Some(8.0),
        ..Default::default()
    };
    let mut response = openai(20_000);
    response["model"] = json!("custom-model");
    response["service_tier"] = json!("priority");
    close(&estimate(&options, &response)["estimated_usd"], 0.056);
    response["usage"]["input_tokens_details"]["cached_tokens"] = json!(1);
    assert_eq!(estimate(&options, &response)["status"], "unknown");
    options.pricing.llm_cached_input_usd_per_million = Some(0.0);
    assert_eq!(estimate(&options, &response)["status"], "estimated");
    for invalid in [f64::NAN, f64::INFINITY, -1.0] {
        options.pricing.llm_input_usd_per_million = Some(invalid);
        assert!(options.pricing.validate().is_err());
    }
    options.pricing.llm_input_usd_per_million = None;
    assert!(options.pricing.validate().is_err());
}

#[test]
fn running_spend_preserves_known_subtotal_when_calls_have_unknown_cost() {
    let mut spend = Spend::default();
    close(&spend.summary()["estimated_total_usd"], 0.0);
    spend.observe(&json!({"estimated_usd":0.25}));
    spend.observe(&unknown("timeout"));
    spend.observe(&json!({"estimated_usd":0.75}));
    let summary = spend.summary();
    assert_eq!(summary["api_calls"], 3);
    assert_eq!(summary["estimated_calls"], 2);
    assert_eq!(summary["unknown_cost_calls"], 1);
    assert_eq!(summary["status"], "incomplete");
    close(&summary["estimated_subtotal_usd"], 1.0);
    assert!(summary["estimated_total_usd"].is_null());
}
