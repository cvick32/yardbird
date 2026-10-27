//! Estimates, not invoices. Prices are frozen in each log; unknown calls never
//! count as free. Output usage already includes reasoning/thinking tokens.
use super::{LlmOptions, LlmProvider};
use anyhow::Context;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

#[derive(clap::Args, Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
#[serde(default)]
pub struct LlmPricing {
    /// Custom effective USD/1M uncached input tokens; requires an output rate.
    #[arg(long)]
    pub llm_input_usd_per_million: Option<f64>,
    /// Custom effective USD/1M output tokens, including reasoning/thinking.
    #[arg(long)]
    pub llm_output_usd_per_million: Option<f64>,
    /// Custom USD/1M cache-read tokens.
    #[arg(long)]
    pub llm_cached_input_usd_per_million: Option<f64>,
    /// Custom USD/1M short cache writes (OpenAI 30m; Anthropic 5m).
    #[arg(long)]
    pub llm_cache_write_usd_per_million: Option<f64>,
    /// Custom USD/1M long cache writes (OpenAI 12h; Anthropic 1h).
    #[arg(long)]
    pub llm_long_cache_write_usd_per_million: Option<f64>,
}

impl LlmPricing {
    pub(super) fn validate(&self) -> anyhow::Result<()> {
        for rate in self.rates().into_iter().flatten() {
            anyhow::ensure!(
                rate.is_finite() && rate >= 0.0,
                "LLM prices must be finite and nonnegative"
            );
        }
        if self != &Self::default() {
            anyhow::ensure!(self.llm_input_usd_per_million.is_some() && self.llm_output_usd_per_million.is_some(),
                "custom LLM pricing requires both --llm-input-usd-per-million and --llm-output-usd-per-million");
        }
        Ok(())
    }

    // Matches TokenUsage::categories(). All categories are disjoint.
    fn rates(&self) -> [Option<f64>; 5] {
        [
            self.llm_input_usd_per_million,
            self.llm_cached_input_usd_per_million,
            self.llm_cache_write_usd_per_million,
            self.llm_long_cache_write_usd_per_million,
            self.llm_output_usd_per_million,
        ]
    }
}

#[derive(Debug, Serialize)]
struct TokenUsage {
    input_tokens: u64,
    uncached_input_tokens: u64,
    cached_input_tokens: u64,
    short_cache_write_tokens: u64,
    long_cache_write_tokens: u64,
    output_tokens: u64,
}

impl TokenUsage {
    fn categories(&self) -> [u64; 5] {
        [
            self.uncached_input_tokens,
            self.cached_input_tokens,
            self.short_cache_write_tokens,
            self.long_cache_write_tokens,
            self.output_tokens,
        ]
    }
}

fn count(value: &Value, name: &str) -> anyhow::Result<u64> {
    value[name]
        .as_u64()
        .with_context(|| format!("missing or invalid usage.{name}"))
}

fn optional_count(value: &Value, name: &str) -> anyhow::Result<u64> {
    if value.get(name).is_none() {
        Ok(0)
    } else {
        count(value, name)
    }
}

fn split_writes(
    total: u64,
    details: &Value,
    short: &str,
    long: &str,
) -> anyhow::Result<(u64, u64)> {
    // Our requests never override the default TTL. Older responses may only
    // supply a total; such writes therefore use the short/default lifetime.
    if details.is_null() {
        return Ok((total, 0));
    }
    let short = count(details, short)?;
    let long = count(details, long)?;
    anyhow::ensure!(
        short.checked_add(long) == Some(total),
        "cache-write breakdown does not match total"
    );
    Ok((short, long))
}

fn usage(provider: LlmProvider, response: &Value) -> anyhow::Result<TokenUsage> {
    let u = &response["usage"];
    let input = count(u, "input_tokens")?;
    let output = count(u, "output_tokens")?;
    let (uncached, cached, short, long, total) = match provider {
        LlmProvider::Openai => {
            let details = &u["input_tokens_details"];
            let cached = count(details, "cached_tokens")?;
            let written = optional_count(details, "cache_write_tokens")?;
            let (short, long) = split_writes(
                written,
                &details["cache_write_tokens_details"],
                "ttl_30m_tokens",
                "ttl_12h_tokens",
            )?;
            let uncached = input
                .checked_sub(cached)
                .and_then(|n| n.checked_sub(written))
                .context("cache tokens exceed input tokens")?;
            (uncached, cached, short, long, input)
        }
        LlmProvider::Anthropic => {
            let cached = count(u, "cache_read_input_tokens")?;
            let written = count(u, "cache_creation_input_tokens")?;
            let (short, long) = split_writes(
                written,
                &u["cache_creation"],
                "ephemeral_5m_input_tokens",
                "ephemeral_1h_input_tokens",
            )?;
            let total = input
                .checked_add(cached)
                .and_then(|n| n.checked_add(written))
                .context("input token count overflow")?;
            (input, cached, short, long, total)
        }
    };
    Ok(TokenUsage {
        input_tokens: total,
        uncached_input_tokens: uncached,
        cached_input_tokens: cached,
        short_cache_write_tokens: short,
        long_cache_write_tokens: long,
        output_tokens: output,
    })
}

fn rates(
    options: &LlmOptions,
    response: &Value,
    tokens: &TokenUsage,
) -> anyhow::Result<(LlmPricing, Value)> {
    if options.pricing != LlmPricing::default() {
        options.pricing.validate()?;
        return Ok((
            options.pricing.clone(),
            json!({"basis":"configured_effective_rates"}),
        ));
    }
    let tier = response
        .get("service_tier")
        .or_else(|| response["usage"].get("service_tier"));
    anyhow::ensure!(
        tier.is_none_or(|v| matches!(v.as_str(), Some("default" | "standard"))),
        "automatic pricing only supports standard service tier; configure effective rates"
    );
    let geo = response["usage"].get("inference_geo");
    anyhow::ensure!(
        geo.is_none_or(|v| v == "global"),
        "automatic pricing only supports global routing"
    );
    // Use the returned model when available; never price an unknown resolved
    // model as the requested one. No prefix/alias guessing.
    let model = response["model"]
        .as_str()
        .or(options.llm_model.as_deref())
        .context("missing model for pricing")?;
    let (mut input, mut output, mut cached, mut short, mut long, source) =
        match (options.llm_provider, model) {
            (LlmProvider::Openai, "gpt-6-astra") => (
                10.0,
                50.0,
                1.0,
                12.5,
                25.0,
                "https://developers.openai.com/api/docs/models/gpt-6-astra",
            ),
            (LlmProvider::Anthropic, "claude-sonnet-5-5") => (
                2.0,
                10.0,
                0.1,
                2.5,
                4.0,
                "https://platform.claude.com/docs/en/about-claude/pricing",
            ),
            (LlmProvider::Anthropic, "claude-sonnet-5") => (
                2.0,
                10.0,
                0.2,
                2.5,
                4.0,
                "https://platform.claude.com/docs/en/about-claude/pricing",
            ),
            (LlmProvider::Anthropic, "claude-sonnet-4-6") => (
                3.0,
                15.0,
                0.3,
                3.75,
                6.0,
                "https://platform.claude.com/docs/en/about-claude/pricing",
            ),
            _ => anyhow::bail!("no pricing preset for {model}; configure effective rates"),
        };
    let long_context = options.llm_provider == LlmProvider::Openai && tokens.input_tokens > 272_000;
    if long_context {
        input *= 2.0;
        cached *= 2.0;
        short *= 2.0;
        long *= 2.0;
        output *= 1.5;
    }
    Ok((
        LlmPricing {
            llm_input_usd_per_million: Some(input),
            llm_output_usd_per_million: Some(output),
            llm_cached_input_usd_per_million: Some(cached),
            llm_cache_write_usd_per_million: Some(short),
            llm_long_cache_write_usd_per_million: Some(long),
        },
        json!({"basis":"published_standard_rates", "model":model, "as_of":"2026-10-23", "source":source, "long_context":long_context}),
    ))
}

pub(super) fn estimate(options: &LlmOptions, response: &Value) -> Value {
    let estimate = || -> anyhow::Result<Value> {
        let tokens = usage(options.llm_provider, response)?;
        let (rates, basis) = rates(options, response, &tokens)?;
        let costs = tokens
            .categories()
            .into_iter()
            .zip(rates.rates())
            .map(|(n, price)| {
                if n == 0 {
                    return Ok(0.0);
                }
                let price = price.context("missing price for a nonzero token category")?;
                Ok(n as f64 * price / 1_000_000.0)
            })
            .collect::<anyhow::Result<Vec<_>>>()?;
        let total: f64 = costs.iter().sum();
        anyhow::ensure!(total.is_finite(), "cost estimate overflow");
        Ok(
            json!({"status":"estimated", "estimated_usd":total, "tokens":tokens,
            "rates_usd_per_million":rates, "pricing":basis,
            "components_usd":{"uncached_input":costs[0], "cached_input":costs[1], "short_cache_write":costs[2], "long_cache_write":costs[3], "output":costs[4]}}),
        )
    };
    match estimate() {
        Ok(value) => value,
        Err(error) => unknown(&format!("{error:#}")),
    }
}

pub(super) fn unknown(reason: &str) -> Value {
    json!({"status":"unknown", "estimated_usd":null, "reason":reason})
}

#[derive(Default)]
pub(super) struct Spend {
    calls: u64,
    unknown_calls: u64,
    subtotal: f64,
}

impl Spend {
    pub fn observe(&mut self, cost: &Value) {
        self.calls += 1;
        match cost["estimated_usd"]
            .as_f64()
            .filter(|v| v.is_finite() && *v >= 0.0)
        {
            Some(value) if (self.subtotal + value).is_finite() => self.subtotal += value,
            _ => self.unknown_calls += 1,
        }
    }

    pub fn summary(&self) -> Value {
        json!({"api_calls":self.calls, "estimated_calls":self.calls - self.unknown_calls,
            "unknown_cost_calls":self.unknown_calls, "estimated_subtotal_usd":self.subtotal,
            "estimated_total_usd":if self.unknown_calls == 0 { Some(self.subtotal) } else { None },
            "status":if self.unknown_calls == 0 { "estimated" } else { "incomplete" }})
    }

    pub fn report(&self) {
        log::info!(
            "LLM spend: ${:.6} estimated subtotal across {} calls; {} calls with unknown cost",
            self.subtotal,
            self.calls,
            self.unknown_calls
        );
    }
}

#[cfg(test)]
mod tests;
