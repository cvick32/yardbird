//! Join quantified clauses against opaque Boolean trace frontiers. Matching
//! supplies correlated tuples; full guarded instances still use shared ranking.
use super::{
    clauses::{source_helpers, ClauseAgenda},
    dependency_search::Goal,
};
use crate::{
    countermodel::{CountermodelTrace, TraceLemma, TraceNode, TraceReason, TraceStatus},
    policy::term_selection::TermCostFactory,
    rule_matching::search_context::SearchContext,
};
use smt2parser::concrete::Term;

pub(crate) fn extend<F: TermCostFactory>(
    trace: &mut CountermodelTrace,
    context: &SearchContext<'_, F>,
) {
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
    for anchor in &anchors {
        if trace.work >= limit {
            trace.budget_exhausted = true;
            return;
        }
        trace.work += 1;
        agenda.add_goal(Goal::new(
            &anchor.expression,
            anchor.model_value.as_deref() != Some("true"),
        ));
    }
    while agenda.pending() > 0 {
        if trace.work + 2 > limit {
            trace.budget_exhausted = true;
            break;
        }
        trace.work += 1;
        let Some(instance) = agenda.step(plan) else {
            continue;
        };
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

fn contains(term: &Term, target: &Term) -> bool {
    term == target
        || matches!(term, Term::Application { arguments, .. } if arguments.iter().any(|a| contains(a, target)))
}
