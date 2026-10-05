//! Explain the enabling requirements of actions encountered by guidance.
//! Requirements and asserted binder bodies are observations, never new lemmas.
use super::*;
use std::collections::{HashMap, HashSet};

pub(super) fn extend<F: TermCostFactory>(
    trace: &mut CountermodelTrace,
    context: &SearchContext<'_, F>,
) {
    let limit = context.allowance.dependency_work;
    let index = context.formulas.index.expect("VMT guidance has an index");
    let plan = context.formulas.quantifiers;
    let types = context.smt.get_array_types();
    let mut actions = HashSet::new();
    let mut helpers = HashSet::new();
    let mut ground = HashMap::<String, Vec<(Term, Term)>>::new();
    let mut seen_bodies = HashSet::new();
    let mut demands = HashMap::<String, Vec<TraceNode>>::new();
    let mut assertions = context.smt.get_asserted_instantiation_terms().into_iter();
    let mut scanned = 0;
    while trace.work < limit && !trace.budget_exhausted {
        if scanned == trace.nodes.len() {
            if demands.is_empty() {
                break;
            }
            let Some(assertion) = assertions.next() else {
                break;
            };
            trace.work += 1;
            for (helper, bodies) in plan.ground_instance_bodies(vec![assertion]) {
                for body in bodies {
                    if !seen_bodies.insert((helper.clone(), body.clone())) {
                        continue;
                    }
                    let name = helper_name(&helper);
                    ground
                        .entry(name.clone())
                        .or_default()
                        .push((helper.clone(), body.clone()));
                    for node in demands.get(&name).into_iter().flatten() {
                        if let Some(conditions) = related_helper(trace, context, node, &helper) {
                            append_body(trace, context, node, body.clone(), conditions);
                        }
                        if trace.budget_exhausted {
                            return;
                        }
                    }
                }
            }
            continue;
        }
        trace.work += 1;
        let node = trace.nodes[scanned].clone();
        scanned += 1;
        let action = match &node.reason {
            TraceReason::Transition {
                frame,
                action: Some(action),
                ..
            } => Some((*frame, action.clone())),
            TraceReason::QuantifiedTransition { frame, .. } => index
                .selected_action(*frame, |term| {
                    charge(trace, limit)?;
                    context
                        .smt
                        .eval_partial(term)?
                        .as_known()
                        .map(str::to_owned)
                        .ok_or_else(|| anyhow::anyhow!("undetermined action"))
                })
                .ok()
                .flatten()
                .map(|action| (*frame, action.to_owned())),
            _ => None,
        };
        if let Some((frame, action)) = action {
            if actions.insert((frame, action.clone())) {
                if let Some(entry) = index.actions().get(&action) {
                    for requirement in &entry.requirements {
                        if charge(trace, limit).is_err() {
                            return;
                        }
                        let mut conditions = Vec::new();
                        let active = requirement.guards.iter().all(|guard| {
                            if charge(trace, limit).is_err() {
                                return false;
                            }
                            let term = index.index_term(&guard.expression, frame);
                            let expected = if guard.required_value {
                                "true"
                            } else {
                                "false"
                            };
                            if context
                                .smt
                                .eval_partial(&term)
                                .is_ok_and(|v| v.as_known() == Some(expected))
                            {
                                conditions.push(Observation {
                                    expression: term,
                                    value: expected.into(),
                                });
                                true
                            } else {
                                false
                            }
                        });
                        if active {
                            append_trace(
                                trace,
                                index,
                                &types,
                                limit,
                                |t| context.smt.eval_partial(t),
                                Some(plan),
                                Some(node.id),
                                TraceStep {
                                    term: index.index_term(&requirement.body, frame),
                                    reason: TraceReason::ActionRequirement {
                                        frame,
                                        action: action.clone(),
                                    },
                                    conditions,
                                    lemma: None,
                                },
                            );
                        }
                        if trace.budget_exhausted {
                            return;
                        }
                    }
                }
            }
        }
        if !matches!(node.status, TraceStatus::Unsupported { .. })
            || !helpers.insert(node.expression.clone())
        {
            continue;
        }
        if !plan.constrains_ground_bodies(&node.expression, node.model_value.as_deref()) {
            continue;
        }
        // Preserve discovery order and replay previously scanned instances for
        // newly reached helpers too. Every link retains its original body and
        // charges comparisons/evaluations to this operation's shared allowance.
        let name = helper_name(&node.expression);
        for (helper, body) in ground.get(&name).into_iter().flatten() {
            if let Some(conditions) = related_helper(trace, context, &node, helper) {
                append_body(trace, context, &node, body.clone(), conditions);
            }
            if trace.budget_exhausted {
                return;
            }
        }
        demands.entry(name).or_default().push(node);
    }
    trace.budget_exhausted |=
        scanned < trace.nodes.len() || (!demands.is_empty() && assertions.len() > 0);
}

fn helper_name(term: &Term) -> String {
    let Term::Application {
        qual_identifier, ..
    } = term
    else {
        unreachable!("ground bodies and demands have binder application heads")
    };
    qual_identifier.get_name()
}

/// Model equality links explanations only; the asserted body is never rewritten.
fn related_helper<F: TermCostFactory>(
    trace: &mut CountermodelTrace,
    context: &SearchContext<'_, F>,
    node: &TraceNode,
    helper: &Term,
) -> Option<Vec<Observation>> {
    charge(trace, context.allowance.dependency_work).ok()?;
    helper_conditions(&node.expression, helper, |equality| {
        charge(trace, context.allowance.dependency_work).ok()?;
        context.smt.eval_partial(equality).ok()
    })
}

fn helper_conditions(
    wanted: &Term,
    helper: &Term,
    mut evaluate: impl FnMut(&Term) -> Option<ModelEvaluation>,
) -> Option<Vec<Observation>> {
    let (
        Term::Application {
            qual_identifier: left,
            arguments: wanted,
        },
        Term::Application {
            qual_identifier: right,
            arguments: actual,
        },
    ) = (wanted, helper)
    else {
        return None;
    };
    if left != right || wanted.len() != actual.len() {
        return None;
    }
    let mut conditions = vec![];
    for (a, b) in wanted.iter().zip(actual) {
        if a == b {
            continue;
        }
        let equality = crate::theories::quantifiers::app("=", vec![a.clone(), b.clone()]);
        if evaluate(&equality)?.as_known() != Some("true") {
            return None;
        }
        conditions.push(Observation {
            expression: equality,
            value: "true".into(),
        });
    }
    Some(conditions)
}

fn append_body<F: TermCostFactory>(
    trace: &mut CountermodelTrace,
    context: &SearchContext<'_, F>,
    node: &TraceNode,
    body: Term,
    mut conditions: Vec<Observation>,
) {
    let limit = context.allowance.dependency_work;
    if charge(trace, limit).is_err() {
        return;
    }
    conditions.push(Observation {
        expression: node.expression.clone(),
        value: node.model_value.clone().unwrap(),
    });
    append_trace(
        trace,
        context.formulas.index.unwrap(),
        &context.smt.get_array_types(),
        limit,
        |t| context.smt.eval_partial(t),
        Some(context.formulas.quantifiers),
        Some(node.id),
        TraceStep {
            term: body,
            reason: TraceReason::AssertedQuantifierBody,
            conditions,
            lemma: None,
        },
    );
}

fn charge(trace: &mut CountermodelTrace, limit: usize) -> anyhow::Result<()> {
    if trace.work >= limit {
        trace.budget_exhausted = true;
        anyhow::bail!("action requirement trace budget exhausted");
    }
    trace.work += 1;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alias_links_are_rechecked_and_preserve_all_captures_and_frames() {
        let wanted: Term = "(all votes@1 r@1)".parse().unwrap();
        let alias: Term = "(all votes@0 maxr@1)".parse().unwrap();
        let linked = helper_conditions(&wanted, &alias, |_| Some("true".into())).unwrap();
        assert_eq!(
            linked
                .iter()
                .map(|c| c.expression.to_string())
                .collect::<Vec<_>>(),
            ["(= votes@1 votes@0)", "(= r@1 maxr@1)"]
        );
        // A new model can break just one capture equality. Neither an old
        // equality, an unknown interpretation, nor an evaluation error is reused.
        for second in [
            Some("false".into()),
            Some(ModelEvaluation::Undetermined),
            None,
        ] {
            assert!(helper_conditions(&wanted, &alias, |term| {
                if term.to_string() == "(= votes@1 votes@0)" {
                    Some("true".into())
                } else {
                    second.clone()
                }
            })
            .is_none());
        }
        assert!(helper_conditions(
            &wanted,
            &"(other votes@1 r@1)".parse().unwrap(),
            |_| panic!("different binders cannot link")
        )
        .is_none());
        assert!(
            helper_conditions(&wanted, &wanted, |_| panic!("exact captures need no query"))
                .unwrap()
                .is_empty()
        );
        assert_eq!(alias.to_string(), "(all votes@0 maxr@1)");
    }
}
