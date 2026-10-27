//! Joint response schema and provider wire formats; no theory semantics live here.
use super::{LlmOptions, LlmProvider};
use crate::policy::instantiation::{InstantiationProposal, InstantiationSnapshot};
use anyhow::Context;
use serde_json::{json, Value};

pub(super) const PROMPT: &str = include_str!("prompt.txt");

fn response_schema(snapshot: &InstantiationSnapshot) -> Value {
    let mut alternatives = vec![json!({"type":"null"})];
    for schema in &snapshot.schemas {
        let properties = schema.slots.keys().map(|slot|
            (slot.clone(), json!({"type":"string", "description":"An ID from the supplied term catalogue, of the slot's required sort."}))
        ).collect::<serde_json::Map<_, _>>();
        alternatives.push(json!({
            "type":"object", "additionalProperties":false,
            "properties": {
                "axiom_id":{"type":"string", "enum":[schema.id]},
                "bindings":{"type":"object", "properties":properties,
                    "required":schema.slots.keys().collect::<Vec<_>>(), "additionalProperties":false}
            }, "required":["axiom_id", "bindings"]
        }));
    }
    json!({"type":"object", "additionalProperties":false,
        "properties":{"proposal":{"anyOf":alternatives}}, "required":["proposal"]})
}

pub(super) fn request(
    options: &LlmOptions,
    snapshot: &InstantiationSnapshot,
    failures: &[Value],
) -> anyhow::Result<Value> {
    let model = options.llm_model.as_deref().context("missing LLM model")?;
    let mut state = snapshot.current_state();
    state["failure_summary"] = json!(failures);
    let block_type = match options.llm_provider {
        LlmProvider::Openai => "input_text",
        LlmProvider::Anthropic => "text",
    };
    let prefix = snapshot.prefix();
    let mut input = Vec::new();
    for (index, part) in prefix.iter().enumerate() {
        let mut block = json!({"type":block_type, "text":serde_json::to_string(part)?});
        // Four explicit boundaries at most: static context and the latest three
        // vocabulary additions. The preceding request's endpoint remains a
        // lookup boundary after an append, without rewriting any block text.
        if options.llm_explicit_cache && (index == 0 || index >= prefix.len().saturating_sub(3)) {
            match options.llm_provider {
                LlmProvider::Openai => {
                    block["prompt_cache_breakpoint"] = json!({"mode":"explicit"})
                }
                LlmProvider::Anthropic => block["cache_control"] = json!({"type":"ephemeral"}),
            }
        }
        input.push(block);
    }
    input.push(json!({"type":block_type,"text":serde_json::to_string(&state)?}));
    let schema = response_schema(snapshot);
    let mut request = match options.llm_provider {
        LlmProvider::Openai => json!({
            "model":model,
            "input":[{"role":"developer", "content":PROMPT.trim()}, {"role":"user", "content":input}],
            "text":{"format":{"type":"json_schema", "name":"array_instantiation", "strict":true, "schema":schema}},
            "max_output_tokens":options.llm_max_output_tokens,
            "store":false, "truncation":"disabled"
        }),
        LlmProvider::Anthropic => json!({
            "model":model, "system":PROMPT.trim(),
            "messages":[{"role":"user", "content":input}],
            "output_config":{"format":{"type":"json_schema", "schema":schema}},
            "max_tokens":options.llm_max_output_tokens
        }),
    };
    if options.llm_explicit_cache && options.llm_provider == LlmProvider::Openai {
        // Suppress implicit writes of the changing model/feedback suffix.
        request["prompt_cache_options"] = json!({"mode":"explicit", "ttl":"30m"});
    }
    if let Some(effort) = &options.llm_reasoning_effort {
        match options.llm_provider {
            LlmProvider::Openai => request["reasoning"] = json!({"effort":effort}),
            LlmProvider::Anthropic => request["output_config"]["effort"] = json!(effort),
        }
    }
    if options.llm_adaptive_thinking {
        request["thinking"] = json!({"type":"adaptive"});
    }
    Ok(request)
}

/// Only completed assistant text is a candidate. Refusals, tool calls, and
/// truncated output never become proposals, even if they contain valid JSON.
pub(super) fn response_text(provider: LlmProvider, response: &Value) -> anyhow::Result<&str> {
    let mut texts = Vec::new();
    match provider {
        LlmProvider::Openai => {
            anyhow::ensure!(
                response["status"] == "completed",
                "OpenAI response not completed: {}",
                response["status"]
            );
            for item in response["output"]
                .as_array()
                .context("missing OpenAI output")?
            {
                match item["type"].as_str() {
                    Some("reasoning") => continue,
                    Some("message") => {
                        anyhow::ensure!(
                            item["role"] == "assistant" && item["status"] == "completed",
                            "incomplete or non-assistant output message"
                        );
                        for block in item["content"]
                            .as_array()
                            .context("missing message content")?
                        {
                            anyhow::ensure!(
                                block["type"] == "output_text",
                                "non-text or refused OpenAI output"
                            );
                            texts.push(block["text"].as_str().context("missing output text")?);
                        }
                    }
                    _ => anyhow::bail!("unexpected OpenAI output item"),
                }
            }
        }
        LlmProvider::Anthropic => {
            anyhow::ensure!(
                response["type"] == "message" && response["role"] == "assistant",
                "not an Anthropic assistant message"
            );
            anyhow::ensure!(
                response["stop_reason"] == "end_turn",
                "Anthropic response not completed: {}",
                response["stop_reason"]
            );
            for block in response["content"]
                .as_array()
                .context("missing Anthropic content")?
            {
                match block["type"].as_str() {
                    Some("thinking" | "redacted_thinking") => continue,
                    Some("text") => {
                        texts.push(block["text"].as_str().context("missing output text")?)
                    }
                    _ => anyhow::bail!("unexpected Anthropic output block"),
                }
            }
        }
    }
    anyhow::ensure!(
        texts.len() == 1,
        "expected exactly one structured text response, got {}",
        texts.len()
    );
    Ok(texts[0])
}

pub(super) fn proposal(text: &str) -> anyhow::Result<Option<InstantiationProposal>> {
    let value: Value = serde_json::from_str(text).context("invalid proposal JSON")?;
    let object = value
        .as_object()
        .context("proposal response must be an object")?;
    anyhow::ensure!(
        object.len() == 1 && object.contains_key("proposal"),
        "response must contain exactly the proposal field"
    );
    if value["proposal"].is_null() {
        Ok(None)
    } else {
        Ok(Some(
            serde_json::from_value(value["proposal"].clone())
                .context("invalid complete proposal")?,
        ))
    }
}
