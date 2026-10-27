//! Compact, model-local failure memory. Full observations stay in the JSONL log.
use std::collections::BTreeMap;

use serde::Serialize;
use serde_json::{json, Value};

#[derive(Default, Serialize)]
pub(super) struct FailureSummary {
    pub total_failures: usize,
    failure_counts: BTreeMap<String, usize>,
    failed_substitutions: Vec<Value>,
    latest_failure: Option<Value>,
}

impl FailureSummary {
    pub fn record(&mut self, request: &Value, response: &Value, feedback: &Value) {
        let reason = feedback["reason"]
            .as_str()
            .or_else(|| feedback["outcome"].as_str())
            .unwrap_or("invalid");
        self.total_failures += 1;
        *self.failure_counts.entry(reason.into()).or_default() += 1;
        let mut failure = json!({"reason":reason});
        for field in [
            "stage",
            "rule",
            "instance",
            "bindings",
            "error",
            "fixed_bindings",
            "binding_slot",
        ] {
            if let Some(value) = feedback.get(field) {
                failure[field] = value.clone();
            }
        }
        if feedback.get("instance").is_none() {
            // Invalid answers may have no grounded tuple. Keep only offered
            // question names and scalar choices, never provider probability tables.
            let selected = request["state"]["selected_axiom"]["id"]
                .as_str()
                .or_else(|| response["answers"]["axiom"]["choice"].as_str());
            let mut choices = serde_json::Map::new();
            if let Some(questions) = request["questions"].as_object() {
                for question in questions.keys() {
                    if question == "axiom"
                        || selected.is_some_and(|id| question.starts_with(&format!("{id}_")))
                    {
                        if let Some(choice) = response["answers"][question]["choice"].as_str() {
                            choices.insert(question.clone(), json!(choice));
                        }
                    }
                }
            }
            failure["choices"] = json!(choices);
        }
        let existing = self
            .failed_substitutions
            .iter_mut()
            .find(|entry| entry["failure"] == failure);
        let entry = if let Some(entry) = existing {
            entry["count"] = json!(entry["count"].as_u64().unwrap() + 1);
            entry.clone()
        } else {
            let entry = json!({"failure":failure,"count":1});
            self.failed_substitutions.push(entry.clone());
            entry
        };
        self.latest_failure = Some(entry);
    }

    pub fn instruction(&self) -> String {
        let Some(latest) = &self.latest_failure else {
            return "Avoid instances listed in successful_instantiations; they are already installed.".into();
        };
        let failure = &latest["failure"];
        let reason = failure["reason"].as_str().unwrap_or("invalid");
        let explanation = match reason {
            "false_antecedent" => "The antecedent was FALSE, making the whole implication TRUE. Choose indices with unequal MODEL VALUES and a false consequent.",
            "true_consequent" => "The consequent was TRUE, making the whole implication TRUE. A violation requires a true antecedent and false consequent.",
            "already_present" => "This instance is already installed or pending and adds no new information.",
            "undetermined" => "The complete formula could not be evaluated to false; unknown is not a violation.",
            "instance_true" => "The complete formula evaluated to TRUE and does not exclude this model.",
            "uninstallable" => "The substitution cannot be installed by Yardbird.",
            "evaluation_error" => "Yardbird could not evaluate this substitution.",
            _ => "The answer was invalid; use the offered axiom and term IDs for all required bindings.",
        };
        let bindings = failure
            .get("bindings")
            .or_else(|| failure.get("choices"))
            .unwrap_or(&Value::Null);
        format!("Latest rejection: rule={}, bindings={bindings}, reason={reason}, repeat_count={}. {explanation} Do not repeat this complete substitution. Consult failure_summary for other rejected tuples and successful_instantiations for installed instances. Seek a NEW complete substitution whose whole formula is FALSE, answering only the questions for the current decision stage. Terms may be reused in different combinations.", failure["rule"], latest["count"])
    }
}
