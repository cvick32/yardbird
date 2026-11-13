//! Join quantified bodies against Boolean trace frontiers and source atoms. Matching
//! supplies correlated tuples; full guarded instances still use shared ranking.
use super::{
    body_matching::BodyAgenda,
    clauses::{source_helpers, ClauseAgenda},
    dependency_search::Goal,
};
use crate::{
    countermodel::{
        append_trace, CountermodelTrace, TraceLemma, TraceNode, TraceReason, TraceStatus, TraceStep,
    },
    policy::term_selection::TermCostFactory,
    rule_matching::search_context::SearchContext,
};
use smt2parser::concrete::Term;

pub(crate) fn extend<F: TermCostFactory>(
    trace: &mut CountermodelTrace,
    context: &SearchContext<'_, F>,
) {
    extend_bodies(trace, context);
    extend_observed_witnesses(trace, context);
    let plan = context.formulas.quantifiers;
    let smt = context.smt;
    let limit = context.allowance.dependency_work;
    let anchors = trace
        .nodes
        .iter()
        .filter(|n| {
            matches!(n.status, TraceStatus::Unsupported { .. })
                && matches!(n.model_value.as_deref(), Some("true" | "false"))
        })
        .cloned()
        .collect::<Vec<_>>();
    let prerequisite_observations = trace
        .nodes
        .iter()
        .any(|node| matches!(node.reason, TraceReason::ActionRequirement { .. }));
    if anchors.is_empty() && !prerequisite_observations {
        return;
    }
    let observed_atoms = trace
        .nodes
        .iter()
        .filter(|node| {
            matches!(node.model_value.as_deref(), Some("true" | "false"))
                && Goal::new(&node.expression, true).key().is_some()
        })
        .map(|node| (node.id, Goal::new(&node.expression, true).atom))
        .collect::<Vec<_>>();
    let mut agenda = ClauseAgenda::default();
    let mut has_demands = false;
    for anchor in &anchors {
        if trace.work >= limit {
            trace.budget_exhausted = true;
            return;
        }
        trace.work += 1;
        has_demands |= agenda.add_demand(
            plan,
            &anchor.expression,
            anchor.model_value.as_deref() == Some("true"),
        );
        agenda.add_goal(Goal::new(
            &anchor.expression,
            anchor.model_value.as_deref() != Some("true"),
        ));
    }
    // Queue observed helper demands before unrelated source clauses so their
    // correlated tuples get the first share of bounded matching work.
    let mut helpers = source_helpers(plan, smt);
    helpers.sort_by_cached_key(ToString::to_string);
    for helper in helpers {
        if trace.work >= limit {
            trace.budget_exhausted = true;
            return;
        }
        trace.work += 1;
        agenda.add_helper(plan, &helper);
    }
    // Witness-body observations may not occur in the source vocabulary. Join
    // these concrete atoms too, keeping their exact captures and model polarity.
    // They propose tuples only; the complete instance is still validated below.
    let join_observations = has_demands || prerequisite_observations;
    if join_observations && !add_trace_observations(trace, &mut agenda, limit) {
        return;
    }
    // Source observations only propose bindings. The complete guarded instance
    // is still checked below; neither source atoms nor model equalities become lemmas.
    let mut sources = if join_observations {
        smt.get_source_subterms()
    } else {
        vec![]
    };
    sources.sort_by_cached_key(ToString::to_string);
    let mut sources = sources.into_iter();
    loop {
        if trace.work + 2 > limit {
            trace.budget_exhausted |= agenda.pending() > 0 || sources.len() > 0;
            break;
        }
        if agenda.pending() == 0 {
            let Some(source) = sources.next() else {
                break;
            };
            trace.work += 1;
            if agenda.wants(source) {
                trace.work += 1;
                if let Ok(value) = smt.eval_partial(source) {
                    match value.as_known() {
                        Some("true") => agenda.add_goal(Goal::new(source, false)),
                        Some("false") => agenda.add_goal(Goal::new(source, true)),
                        _ => {}
                    }
                }
            }
            continue;
        }
        trace.work += 1;
        let Some(instance) = agenda.step_modulo(plan, |left, right| {
            if !join_observations {
                return false;
            }
            if trace.work >= limit {
                trace.budget_exhausted = true;
                return false;
            }
            trace.work += 1;
            smt.eval_partial(&super::app("=", vec![left.clone(), right.clone()]))
                .is_ok_and(|value| value.as_known() == Some("true"))
        }) else {
            continue;
        };
        if trace.work >= limit {
            trace.budget_exhausted = true;
            break;
        }
        trace.work += 1;
        if !smt
            .eval_partial(&instance.term)
            .is_ok_and(|v| v.as_known() == Some("false"))
        {
            continue;
        }
        // Every match is rooted in the observed atom syntax. Keep those links
        // alongside the entire axiom, rather than asserting observed values.
        let roots = observed_atoms
            .iter()
            .filter(|(_, atom)| contains(&instance.term, atom))
            .map(|(id, _)| *id)
            .collect::<Vec<_>>();
        if roots.is_empty() {
            continue;
        }
        trace.nodes.push(TraceNode {
            id: trace.nodes.len(),
            parent: roots.first().copied(),
            expression: instance.term.clone(),
            model_value: Some("false".into()),
            reason: TraceReason::QuantifierMatch { anchors: roots },
            conditions: vec![],
            lemma: Some(TraceLemma {
                rule: instance.rule.name().to_owned(),
                formula: instance.term.clone(),
                model_value: Some("false".into()),
                instance: Some(instance),
            }),
            status: TraceStatus::ViolatedQuantifierInstance,
        });
    }
}

/// An earlier-frame observation can suggest the quantified values of a false
/// existential at this frame. Keep the demanded helper's captures unchanged,
/// and trace its actual body: a satisfied introduction may expose missing frame
/// instances rather than directly refuting the existential abstraction.
fn extend_observed_witnesses<F: TermCostFactory>(
    trace: &mut CountermodelTrace,
    context: &SearchContext<'_, F>,
) {
    let plan = context.formulas.quantifiers;
    let limit = context.allowance.dependency_work;
    let mut agenda = ClauseAgenda::default();
    let mut roots = Vec::new();
    for node in trace.nodes.iter().filter(|node| {
        node.model_value.as_deref() == Some("false")
            && matches!(node.status, TraceStatus::Unsupported { .. })
    }) {
        if trace.work >= limit {
            trace.budget_exhausted = true;
            return;
        }
        trace.work += 1;
        if agenda.add_demand(plan, &node.expression, false) {
            roots.push((node.id, node.expression.clone()));
        }
    }
    if roots.is_empty() || !add_trace_observations(trace, &mut agenda, limit) {
        return;
    }
    while agenda.pending() > 0 && trace.work < limit {
        trace.work += 1;
        let instance = agenda.step_capture_hints(plan, |left, right| {
            if trace.work >= limit {
                trace.budget_exhausted = true;
                return false;
            }
            trace.work += 1;
            context
                .smt
                .eval_partial(&super::app("=", vec![left.clone(), right.clone()]))
                .is_ok_and(|value| value.as_known() == Some("true"))
        });
        let Some(instance) = instance else { continue };
        let anchors = roots
            .iter()
            .filter(|(_, helper)| contains(&instance.term, helper))
            .map(|(id, _)| *id)
            .collect::<Vec<_>>();
        let Some(parent) = anchors.first().copied() else {
            continue;
        };
        // False-existential demands produce only introductions B => E.
        let Term::Application { arguments, .. } = &instance.term else {
            continue;
        };
        let body = arguments[0].clone();
        append_trace(
            trace,
            context
                .formulas
                .index
                .expect("VMT guidance requires an index"),
            &context.smt.get_array_types(),
            limit,
            |term| context.smt.eval_partial(term),
            Some(plan),
            Some(parent),
            TraceStep {
                frontier: None,
                term: body,
                reason: TraceReason::QuantifierMatch { anchors },
                conditions: vec![],
                lemma: Some(TraceLemma {
                    rule: instance.rule.name().to_owned(),
                    formula: instance.term.clone(),
                    model_value: None,
                    instance: Some(instance),
                }),
            },
        );
        if trace.budget_exhausted {
            break;
        }
    }
    trace.budget_exhausted |= agenda.pending() > 0 && trace.work >= limit;
}

/// Observations propose bindings, never asserted facts. Keep model polarity
/// and literal capture terms while excluding unknown values.
fn add_trace_observations(
    trace: &mut CountermodelTrace,
    agenda: &mut ClauseAgenda,
    limit: usize,
) -> bool {
    let mut seen = std::collections::HashSet::new();
    for node in &trace.nodes {
        if trace.work >= limit {
            trace.budget_exhausted = true;
            return false;
        }
        trace.work += 1;
        let truth = match node.model_value.as_deref() {
            Some("true") => true,
            Some("false") => false,
            _ => continue,
        };
        if agenda.wants(&node.expression) && seen.insert((node.expression.clone(), truth)) {
            agenda.add_goal(Goal::new(&node.expression, !truth));
        }
    }
    true
}

/// Compare scoped quantified bodies rather than their unrelated helper names.
/// A match only chooses a tuple. Trace the resulting body even when its outer
/// introduction is satisfied: a false inner forall has its own witness path.
fn extend_bodies<F: TermCostFactory>(
    trace: &mut CountermodelTrace,
    context: &SearchContext<'_, F>,
) {
    let plan = context.formulas.quantifiers;
    let limit = context.allowance.dependency_work;
    let mut bodies = BodyAgenda::with_candidate_hints();
    let mut helpers = source_helpers(plan, context.smt);
    helpers.sort_by_cached_key(ToString::to_string);
    let mut anchors = Vec::new();
    let mut scanned = 0;
    loop {
        for node in &trace.nodes[scanned..] {
            if node.model_value.as_deref() == Some("false")
                && matches!(node.status, TraceStatus::Unsupported { .. })
            {
                if trace.work >= limit {
                    trace.budget_exhausted = true;
                    return;
                }
                trace.work += 1;
                if bodies.add_demand(plan, &node.expression) {
                    anchors.push((node.id, node.expression.clone()));
                }
            }
        }
        scanned = trace.nodes.len();
        if anchors.is_empty() {
            return;
        }
        // Source helpers propose tuples; even inactive helpers are safe hints.
        // Only the original guarded instance can become a refinement lemma.
        for helper in helpers.drain(..) {
            if trace.work >= limit {
                trace.budget_exhausted = true;
                return;
            }
            trace.work += 1;
            bodies.add_source(plan, &helper);
        }
        if bodies.pending() == 0 {
            return;
        }
        if trace.work >= limit {
            trace.budget_exhausted = true;
            return;
        }
        trace.work += 1;
        let result = bodies.step(plan, |term| {
            if trace.work >= limit {
                trace.budget_exhausted = true;
                anyhow::bail!("countermodel body matching budget exhausted");
            }
            trace.work += 1;
            Ok(context
                .smt
                .eval_partial(term)?
                .as_known()
                .unwrap_or("<undetermined>")
                .to_owned())
        });
        let Ok(Some((instance, _))) = result else {
            continue;
        };
        let roots = anchors
            .iter()
            .filter(|(_, term)| contains(&instance.term, term))
            .map(|(id, _)| *id)
            .collect::<Vec<_>>();
        let Some(parent) = roots.first().copied() else {
            continue;
        };
        // BodyAgenda's demand matches return existential introductions B => E.
        let Term::Application { arguments, .. } = &instance.term else {
            continue;
        };
        let body = arguments[0].clone();
        append_trace(
            trace,
            context
                .formulas
                .index
                .expect("VMT guidance requires an index"),
            &context.smt.get_array_types(),
            limit,
            |term| context.smt.eval_partial(term),
            Some(plan),
            Some(parent),
            TraceStep {
                frontier: None,
                term: body,
                reason: TraceReason::QuantifierMatch { anchors: roots },
                conditions: vec![],
                lemma: Some(TraceLemma {
                    rule: instance.rule.name().to_owned(),
                    formula: instance.term.clone(),
                    model_value: None,
                    instance: Some(instance),
                }),
            },
        );
    }
}

fn contains(term: &Term, target: &Term) -> bool {
    term == target
        || matches!(term, Term::Application { arguments, .. } if arguments.iter().any(|a| contains(a, target)))
}

#[cfg(test)]
mod observation_tests {
    use super::*;
    use crate::theories::quantifiers::{BinderKind, BinderRule, QuantifierPlan};
    use smt2parser::{concrete::Symbol, vmt::array_abstractor::string_to_sort};

    #[test]
    fn witness_body_observations_join_without_source_atoms_or_capture_changes() {
        let int = string_to_sort("Int");
        let rule = BinderRule {
            name: "q".into(),
            kind: BinderKind::Forall,
            captures: vec![(Symbol("state".into()), int.clone())],
            variables: vec![(Symbol("x".into()), int.clone()), (Symbol("y".into()), int)],
            body: "(=> (p state x) (r state y))".parse().unwrap(),
            witnesses: vec![],
            result_sort: string_to_sort("Bool"),
            unit_capture: false,
        };
        let expected = rule.instantiate(
            &["state@1".parse().unwrap()],
            &["1".parse().unwrap(), "2".parse().unwrap()],
        );
        let mut plan = QuantifierPlan::default();
        plan.rules.push(rule);
        let mut trace = CountermodelTrace {
            model_version: 7,
            depth: 1,
            transition_order: Default::default(),
            work: 0,
            budget_exhausted: false,
            nodes: vec![],
        };
        for (expression, value) in [
            ("(p state@1 1)", Some("true")),
            ("(r state@1 2)", Some("false")),
            ("(r state@1 3)", None),
            ("(p state@1 1)", Some("true")),
        ] {
            trace.nodes.push(TraceNode {
                id: trace.nodes.len(),
                parent: None,
                expression: expression.parse().unwrap(),
                model_value: value.map(str::to_owned),
                reason: TraceReason::AssertedQuantifierBody,
                conditions: vec![],
                lemma: None,
                status: TraceStatus::Value,
            });
        }
        let mut agenda = ClauseAgenda::default();
        assert!(agenda.add_demand(&plan, &"(q state@1)".parse().unwrap(), true));
        assert!(add_trace_observations(&mut trace, &mut agenda, 32));
        let mut instances = vec![];
        while agenda.pending() > 0 {
            instances.extend(agenda.step(&plan));
        }
        assert_eq!(instances.len(), 1);
        assert_eq!(instances[0].term, expected);
        assert_eq!(trace.work, 4);
        assert!(!trace.budget_exhausted);
        assert!(trace.nodes.iter().all(|n| n.lemma.is_none()));
        assert!(!add_trace_observations(&mut trace, &mut agenda, 4));
        assert!(trace.budget_exhausted);
    }
}
