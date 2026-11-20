//! Bedrock tool wire format and exact indexed retrieval. No solver operations.
use crate::policy::{instantiation::InstantiationProposal, llm::LlmOptions};
use serde::Deserialize;
use serde_json::{json, Value};

pub(super) const PROMPT: &str = "You advise a running Yardbird verifier. Ordinary search and solver checks continue while you reason. Use pinned context to identify missing proof relationships and propose complete, typed schema substitutions. Model equalities are observations, never proof facts. Include a concise public rationale explaining the intended proof step or how proposal IDs connect. Each instance is independently revalidated on the live model. Only Yardbird establishes proof progress. Use read_context/inspect for exact records, expand_action for encountered prerequisites. Bind each instantiate slot directly with a ground SMT-LIB term or a pinned term ID. snapshot explicitly refreshes the pin. yield ends this agent episode, never verification. You cannot schedule search, advance, or stop. Return one tool call at a time. No private reasoning transcript is requested.";

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct Item {
    pub proposal_id: String,
    pub proposal: InstantiationProposal,
    #[serde(default)]
    pub rationale: Option<String>,
}

#[derive(Deserialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum Decision {
    ContinueSymbolic,
    Advise,
}

#[derive(Deserialize)]
#[serde(tag = "tool", rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum Tool {
    Assess {
        epoch: String,
        decision: Decision,
        reason: String,
        next_refinements: u32,
    },
    Snapshot {
        epoch: String,
    },
    Inspect {
        epoch: String,
        r#ref: String,
    },
    ReadContext {
        epoch: String,
        section: String,
        #[serde(default)]
        r#ref: Option<String>,
        #[serde(default)]
        query: Option<String>,
        #[serde(default)]
        offset: usize,
        #[serde(default = "default_limit")]
        limit: usize,
    },
    MakeTerm {
        epoch: String,
        smt2: String,
    },
    Instantiate {
        epoch: String,
        items: Vec<Value>,
        #[serde(default)]
        rationale: Option<String>,
    },
    ExpandAction {
        epoch: String,
        r#ref: String,
        work: usize,
    },
    Yield {
        epoch: String,
        reason: String,
    },
}
fn default_limit() -> usize {
    20
}
impl Tool {
    pub fn epoch(&self) -> &str {
        match self {
            Self::Assess { epoch, .. }
            | Self::Snapshot { epoch }
            | Self::Inspect { epoch, .. }
            | Self::ReadContext { epoch, .. }
            | Self::MakeTerm { epoch, .. }
            | Self::Instantiate { epoch, .. }
            | Self::ExpandAction { epoch, .. }
            | Self::Yield { epoch, .. } => epoch,
        }
    }
}

pub(super) fn tools() -> Value {
    serde_json::from_str(include_str!("tools.json")).expect("invalid agent tool definitions")
}

pub(super) fn request(config: &LlmOptions, history: &[Value]) -> Value {
    let mut r = json!({"model":config.llm_model,"input":history,"tools":tools(),"tool_choice":"required",
        "parallel_tool_calls":false,"max_output_tokens":config.llm_max_output_tokens,
        "store":false,"include":["reasoning.encrypted_content"],"truncation":"disabled"});
    if let Some(effort) = &config.llm_reasoning_effort {
        r["reasoning"] = json!({"effort":effort});
    }
    r
}

pub(super) fn decode(response: &Value) -> anyhow::Result<(String, String, Tool)> {
    anyhow::ensure!(
        response["status"] == "completed",
        "provider response is incomplete"
    );
    let output = response["output"]
        .as_array()
        .ok_or_else(|| anyhow::anyhow!("missing response output"))?;
    let calls: Vec<_> = output
        .iter()
        .filter(|i| i["type"] == "function_call")
        .collect();
    anyhow::ensure!(calls.len() == 1, "expected exactly one tool call");
    let call = calls[0];
    let name = call["name"]
        .as_str()
        .ok_or_else(|| anyhow::anyhow!("missing tool name"))?;
    let id = call["call_id"]
        .as_str()
        .ok_or_else(|| anyhow::anyhow!("missing call ID"))?;
    let mut args: Value = serde_json::from_str(
        call["arguments"]
            .as_str()
            .ok_or_else(|| anyhow::anyhow!("missing arguments"))?,
    )?;
    let object = args
        .as_object_mut()
        .ok_or_else(|| anyhow::anyhow!("arguments must be an object"))?;
    anyhow::ensure!(!object.contains_key("tool"), "unexpected tool argument");
    object.insert("tool".into(), json!(name));
    Ok((id.into(), name.into(), serde_json::from_value(args)?))
}

pub(super) fn retrieve(
    value: &Value,
    reference: Option<&str>,
    query: Option<&str>,
    offset: usize,
    limit: usize,
) -> anyhow::Result<Value> {
    anyhow::ensure!(limit > 0, "limit must be positive");
    if let Some(text) = value.as_str() {
        anyhow::ensure!(reference.is_none(), "text sections do not have IDs");
        let text = if let Some(q) = query {
            text.lines()
                .filter(|l| l.contains(q))
                .collect::<Vec<_>>()
                .join("\n")
        } else {
            text.into()
        };
        let total = text.chars().count();
        let part: String = text.chars().skip(offset).take(limit.min(16000)).collect();
        let next = offset.saturating_add(part.chars().count());
        return Ok(
            json!({"text":part,"total":total,"offset":offset,"next_offset":(next<total).then_some(next)}),
        );
    }
    let entries: Vec<&Value> = match value {
        Value::Array(v) => v.iter().collect(),
        Value::Object(v) => v.values().collect(),
        _ => anyhow::bail!("section is not retrievable"),
    };
    let matches: Vec<_> = entries
        .into_iter()
        .filter(|v| {
            reference.is_none_or(|id| v["id"] == id)
                && query.is_none_or(|q| v.to_string().contains(q))
        })
        .collect();
    let selected: Vec<_> = matches.iter().skip(offset).take(limit.min(50)).collect();
    let next = offset.saturating_add(selected.len());
    Ok(
        json!({"items":selected,"total":matches.len(),"offset":offset,"next_offset":(next<matches.len()).then_some(next)}),
    )
}
