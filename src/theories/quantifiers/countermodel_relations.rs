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
    if anchors.is_empty() {
        return;
    }
    let mut agenda = ClauseAgenda::default();
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
    // Source observations only propose bindings. The complete guarded instance
    // is still checked below; neither source atoms nor model equalities become lemmas.
    let mut sources = if has_demands {
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
            if !has_demands {
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
        let roots = anchors
            .iter()
            .filter(|n| contains(&instance.term, &n.expression))
            .map(|n| n.id)
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
