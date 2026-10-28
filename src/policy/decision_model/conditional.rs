//! Beam search with a fresh conditional distribution for each retained prefix.
use serde_json::{json, Value};

use super::{
    ranked_bindings::RankedBindings, snapshot::Snapshot, term_choices::TermChoiceSearch, Experiment,
};
use crate::policy::discovery::DiscoveryContext;

pub(super) enum Outcome {
    Complete(Vec<RankedBindings>),
    Invalid {
        request: Value,
        response: Value,
        error: String,
    },
    Stopped,
}

struct Prefix {
    response: Value,
    log_score: f64,
    matches_model_choice: bool,
}

impl Experiment {
    pub(super) fn binding_choices(
        &mut self,
        context: &DiscoveryContext<'_>,
        attempt: usize,
        original: &Value,
        keep: usize,
    ) -> anyhow::Result<Outcome> {
        let mut search = TermChoiceSearch::new(original, self.options.jev_beam_width, keep)?;
        while !search.is_complete() {
            let stage = search.stage();
            let request = search.request();
            let Some((response, elapsed)) = self.query(context, attempt, stage, &request)? else {
                return Ok(Outcome::Stopped);
            };
            let result = search.advance(&response);
            let error = result.as_ref().err().map(ToString::to_string);
            self.record(context, json!({"event":"binding_result", "attempt":attempt,
                "stage":stage, "slot":original["state"]["binding_slot"],
                "fixed_bindings":request["state"]["fixed_bindings"],
                "response":response,"elapsed_secs":elapsed,"cost":super::query_cost(&response, &self.options),
                "outcome":if error.is_some() { "invalid" } else { "selected" },"error":error}))?;
            if let Err(error) = result {
                return Ok(Outcome::Invalid {
                    request,
                    response,
                    error: error.to_string(),
                });
            }
        }
        Ok(Outcome::Complete(search.results()))
    }

    pub(super) fn conditional_bindings(
        &mut self,
        context: &DiscoveryContext<'_>,
        attempt: usize,
        snapshot: &Snapshot,
        full_request: &Value,
    ) -> anyhow::Result<Outcome> {
        let order = snapshot.binding_order(full_request)?;
        let mut beam = vec![Prefix {
            response: json!({"answers":{}}),
            log_score: 0.0,
            matches_model_choice: true,
        }];
        for (step, slot) in order.iter().enumerate() {
            let last = step + 1 == order.len();
            let keep = if last {
                self.options.jev_candidates
            } else {
                self.options.jev_beam_width
            };
            let mut expanded = Vec::new();
            for prefix in &beam {
                let request = snapshot.conditional_request(full_request, &prefix.response, slot)?;
                let ranked = match self.binding_choices(context, attempt, &request, keep)? {
                    Outcome::Complete(ranked) => ranked,
                    outcome => return Ok(outcome),
                };
                for candidate in ranked.into_iter().take(keep) {
                    let p = candidate
                        .probability_product
                        .expect("validated probability table");
                    if p == 0.0 {
                        continue;
                    }
                    let mut answers = prefix.response["answers"].as_object().unwrap().clone();
                    answers.extend(candidate.response["answers"].as_object().unwrap().clone());
                    expanded.push(Prefix {
                        response: json!({"answers":answers}),
                        log_score: prefix.log_score + p.ln(),
                        matches_model_choice: prefix.matches_model_choice
                            && candidate.matches_model_choice,
                    });
                }
            }
            expanded.sort_by(|a, b| {
                b.log_score
                    .total_cmp(&a.log_score)
                    .then_with(|| a.response.to_string().cmp(&b.response.to_string()))
            });
            expanded.truncate(keep);
            beam = expanded;
        }
        Ok(Outcome::Complete(
            beam.into_iter()
                .map(|prefix| RankedBindings {
                    response: prefix.response,
                    probability_product: Some(prefix.log_score.exp()),
                    matches_model_choice: prefix.matches_model_choice,
                })
                .collect(),
        ))
    }
}
