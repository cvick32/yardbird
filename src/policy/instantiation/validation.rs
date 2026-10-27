//! Shared acceptance checks; provider responses never bypass model validation.
use crate::{
    instance_installation::assertion_tracker::canonical_instantiation_key,
    policy::discovery::DiscoveryContext, rule_matching::candidate::SymbolicInstance,
    solver::api::ModelEvaluation,
};
use serde_json::{json, Value};
use smt2parser::concrete::Term;

pub(crate) fn validate(
    context: &DiscoveryContext<'_>,
    instance: SymbolicInstance,
) -> (Value, Option<SymbolicInstance>) {
    let mut feedback = json!({"rule":instance.rule.name(),"instance":instance.term.to_string(),
        "bindings":instance.bindings.iter().map(|(v,t)| (v.clone(), t.to_string())).collect::<std::collections::BTreeMap<_,_>>()});
    let Some(normalized) = context
        .smt
        .make_unquantified_instance(instance.term.clone())
    else {
        feedback["outcome"] = json!("uninstallable");
        return (feedback, None);
    };
    let key = canonical_instantiation_key(normalized.get_term());
    if context.pending.contains(&key)
        || context
            .smt
            .get_instantiations()
            .iter()
            .any(|t| canonical_instantiation_key(t) == key)
    {
        feedback["outcome"] = json!("already_present");
        return (feedback, None);
    }
    let evaluation = context.smt.eval_partial(&instance.term);
    match evaluation {
        Ok(ModelEvaluation::Known(value)) if value.trim() == "false" => {
            feedback["outcome"] = json!("violated");
            feedback["model_value"] = json!(false);
            (feedback, Some(instance))
        }
        result => {
            let outcome = match &result {
                Ok(ModelEvaluation::Known(v)) if v.trim() == "true" => "instance_true",
                Ok(_) => "undetermined",
                Err(_) => "evaluation_error",
            };
            feedback["outcome"] = json!(outcome);
            if let Err(error) = result {
                feedback["error"] = json!(error.to_string());
            }
            let mut observations = std::collections::BTreeMap::new();
            observe_subterms(context, &instance.term, &mut observations);
            let mut reason = outcome;
            if outcome == "instance_true" {
                if let Term::Application {
                    qual_identifier,
                    arguments,
                } = &instance.term
                {
                    if qual_identifier.to_string() == "=>" && arguments.len() == 2 {
                        let value = |term: &Term| {
                            observations
                                .get(&term.to_string())
                                .and_then(|v| v["value"].as_str())
                        };
                        if value(&arguments[0]) == Some("false") {
                            reason = "false_antecedent";
                        } else if value(&arguments[1]) == Some("true") {
                            reason = "true_consequent";
                        }
                    }
                }
            }
            feedback["reason"] = json!(reason);
            feedback["observations"] = json!(observations);
            feedback["explanation"] = json!("Only a new, installable instance whose COMPLETE formula evaluates to false excludes this model. A false antecedent makes an implication true. Unknown evaluations are not false. Try a different complete substitution using the original model and this feedback.");
            (feedback, None)
        }
    }
}

fn observe_subterms(
    context: &DiscoveryContext<'_>,
    term: &Term,
    observations: &mut std::collections::BTreeMap<String, Value>,
) {
    let key = term.to_string();
    if observations.contains_key(&key) {
        return;
    }
    let value = match context.smt.eval_partial(term) {
        Ok(ModelEvaluation::Known(value)) => json!({"status":"known","value":value}),
        Ok(ModelEvaluation::Undetermined) => json!({"status":"undetermined"}),
        Err(error) => json!({"status":"error","error":error.to_string()}),
    };
    observations.insert(key, value);
    if let Term::Application { arguments, .. } = term {
        for argument in arguments {
            observe_subterms(context, argument, observations);
        }
    }
}
