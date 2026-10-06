//! Read-only explanations of one counter-model. These observations are not proofs
//! or asserted equalities; the refinement policy remains independent of tracing.
use crate::policy::effort::GuidanceTransitionOrder;
use serde::{Deserialize, Serialize};
use smt2parser::concrete::Term;
use std::collections::VecDeque;

use crate::{
    policy::term_selection::TermCostFactory,
    rule_matching::{
        candidate::SymbolicInstance, provenance::CountermodelOrigin, search_context::SearchContext,
        symbolic_pool::SymbolicCandidatePool,
    },
    solver::api::ModelEvaluation,
    theories::quantifiers::{
        countermodel::{InitializerSearch, TransitionSearch},
        countermodel_relations, QuantifierPlan,
    },
    transition_index::TransitionIndex,
};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Observation {
    #[serde(with = "term_text")]
    pub expression: Term,
    pub value: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TraceLemma {
    pub rule: String,
    #[serde(with = "term_text")]
    pub formula: Term,
    pub model_value: Option<String>,
    #[serde(skip)]
    pub(crate) instance: Option<SymbolicInstance>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TraceReason {
    PropertyViolation,
    Definition,
    /// Each child is an alternative explanation, or all children are needed.
    BooleanBranch {
        alternatives: bool,
    },
    Argument {
        index: usize,
    },
    Conditional,
    Transition {
        frame: u16,
        action: Option<String>,
        #[serde(with = "term_text")]
        assignment: Term,
    },
    ArrayAxiom,
    Initialization {
        path: Vec<TraceLemma>,
    },
    /// An exact guarded instance whose truth guidance could not determine.
    /// Standard generation may validate it; tracing cannot use its equation.
    UnresolvedInitialization {
        path: Vec<TraceLemma>,
        expression: String,
    },
    /// A pointwise transition equation, with every enclosing binder retained.
    QuantifiedTransition {
        frame: u16,
        path: Vec<TraceLemma>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        unresolved: Option<String>,
    },
    QuantifierMatch {
        anchors: Vec<usize>,
    },
    /// Witness implication or justified body for a false forall / true exists.
    QuantifierWitness,
    /// A requirement of an action reached by the value trace, at its source frame.
    ActionRequirement {
        frame: u16,
        action: String,
    },
    /// An already asserted body; model-equal captures are recorded as conditions.
    AssertedQuantifierBody,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TraceStatus {
    Expanded,
    Value,
    InitialState { array: String },
    Unsupported { detail: String },
    EvaluationFailed { detail: String },
    Undetermined { expression: String },
    ViolatedArrayAxiom,
    ViolatedQuantifierInstance,
    InconsistentStep,
    Cycle,
    BudgetExhausted,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TraceNode {
    pub id: usize,
    pub parent: Option<usize>,
    #[serde(with = "term_text")]
    pub expression: Term,
    pub model_value: Option<String>,
    pub reason: TraceReason,
    pub conditions: Vec<Observation>,
    pub lemma: Option<TraceLemma>,
    pub status: TraceStatus,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CountermodelTrace {
    pub model_version: u64,
    pub depth: u16,
    #[serde(default)]
    pub transition_order: GuidanceTransitionOrder,
    pub work: usize,
    pub budget_exhausted: bool,
    pub nodes: Vec<TraceNode>,
}

impl CountermodelTrace {
    pub(crate) fn unresolved_instances(
        &self,
    ) -> impl Iterator<Item = (SymbolicInstance, CountermodelOrigin)> + '_ {
        self.nodes.iter().filter_map(|node| {
            let unresolved = match node.reason {
                TraceReason::UnresolvedInitialization { .. } => true,
                TraceReason::QuantifiedTransition { ref unresolved, .. } => unresolved.is_some(),
                TraceReason::QuantifierWitness | TraceReason::QuantifierMatch { .. } => {
                    matches!(node.status, TraceStatus::Undetermined { .. })
                }
                _ => false,
            };
            if !unresolved {
                return None;
            }
            let instance = node.lemma.as_ref()?.instance.clone()?;
            Some((
                instance,
                CountermodelOrigin {
                    model_version: self.model_version,
                    depth: self.depth,
                    node: node.id,
                },
            ))
        })
    }

    pub(crate) fn candidate_pool(&self) -> SymbolicCandidatePool {
        let mut pool = SymbolicCandidatePool::default();
        for node in &self.nodes {
            if !matches!(
                node.status,
                TraceStatus::ViolatedArrayAxiom | TraceStatus::ViolatedQuantifierInstance
            ) {
                continue;
            }
            if let Some(instance) = node
                .lemma
                .as_ref()
                .and_then(|lemma| lemma.instance.as_ref())
            {
                pool.remember_traced(
                    instance.clone(),
                    CountermodelOrigin {
                        model_version: self.model_version,
                        depth: self.depth,
                        node: node.id,
                    },
                );
            }
        }
        pool
    }
}

pub(crate) enum TraceError {
    Budget,
    Evaluation(String),
    Undetermined(String),
}

/// Both traversal steps and model queries consume work. The caller owns the
/// model lifetime; no solver value is retained as a logical constraint.
pub(crate) struct TraceContext<'a> {
    pub index: &'a TransitionIndex,
    pub types: &'a [(String, String)],
    evaluate: &'a mut dyn FnMut(&Term) -> anyhow::Result<ModelEvaluation>,
    remaining: usize,
    initializers: Option<InitializerSearch<'a>>,
    transitions: Option<TransitionSearch<'a>>,
}
impl TraceContext<'_> {
    pub fn charge(&mut self) -> Result<(), TraceError> {
        self.remaining = self.remaining.checked_sub(1).ok_or(TraceError::Budget)?;
        Ok(())
    }
    pub fn observe(&mut self, term: &Term) -> Result<Observation, TraceError> {
        self.charge()?;
        let value = (self.evaluate)(term).map_err(|e| TraceError::Evaluation(e.to_string()))?;
        let ModelEvaluation::Known(value) = value else {
            return Err(TraceError::Undetermined(term.to_string()));
        };
        Ok(Observation {
            expression: term.clone(),
            value: value.trim().to_owned(),
        })
    }
    pub fn boolean(&mut self, term: &Term) -> Result<Observation, TraceError> {
        let observation = self.observe(term)?;
        if !matches!(observation.value.as_str(), "true" | "false") {
            return Err(TraceError::Evaluation(format!(
                "expected Boolean value for {term}, got {}",
                observation.value
            )));
        }
        Ok(observation)
    }
}

pub(crate) struct TraceStep {
    pub term: Term,
    pub reason: TraceReason,
    pub conditions: Vec<Observation>,
    pub lemma: Option<TraceLemma>,
    /// A branch-local failure already observed while discovering alternatives.
    /// Retain it as a trace frontier without repeating the model query.
    pub frontier: Option<TraceError>,
}

/// Guided search consumes the same borrowed formulas, model and allowance as
/// ordinary refinement. Its traversal and partial evaluation remain local.
pub(crate) fn search<F: TermCostFactory>(context: &SearchContext<'_, F>) -> CountermodelTrace {
    let mut trace = trace_refinement(
        context
            .formulas
            .index
            .expect("VMT guidance requires a formula index"),
        &context.smt.get_array_types(),
        context.depth,
        context.model_version,
        context.allowance.dependency_work,
        |term| context.smt.eval_partial(term),
        Some(context.formulas.quantifiers),
        context.allowance.guidance_transition_order,
    );
    countermodel_relations::extend(&mut trace, context);
    use crate::policy::effort::ActionRequirementGuidance;
    if match context.allowance.guidance_action_requirements {
        ActionRequirementGuidance::Disabled => false,
        ActionRequirementGuidance::WhenUnproductive => {
            !trace.budget_exhausted
                && trace
                    .nodes
                    .iter()
                    .all(|node| matches!(node.status, TraceStatus::Expanded | TraceStatus::Value))
        }
        ActionRequirementGuidance::Always => true,
    } {
        requirements::extend(&mut trace, context);
    }
    trace
}
impl TraceStep {
    fn child(term: Term, reason: TraceReason) -> Self {
        Self {
            term,
            reason,
            conditions: vec![],
            lemma: None,
            frontier: None,
        }
    }
}

/// Explain reads in the false, grounded property at `depth`, without installing
/// anything. Unsupported leaves and truncated work remain explicit frontiers.
/// The result is available independently of profiling to future analyses/policies.
pub fn trace_violation(
    index: &TransitionIndex,
    types: &[(String, String)],
    depth: u16,
    model_version: u64,
    work_limit: usize,
    evaluate: impl FnMut(&Term) -> anyhow::Result<ModelEvaluation>,
) -> CountermodelTrace {
    trace_refinement(
        index,
        types,
        depth,
        model_version,
        work_limit,
        evaluate,
        None,
        GuidanceTransitionOrder::PredecessorOnly,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn trace_refinement(
    index: &TransitionIndex,
    types: &[(String, String)],
    depth: u16,
    model_version: u64,
    work_limit: usize,
    evaluate: impl FnMut(&Term) -> anyhow::Result<ModelEvaluation>,
    plan: Option<&QuantifierPlan>,
    transition_order: GuidanceTransitionOrder,
) -> CountermodelTrace {
    let mut trace = CountermodelTrace {
        model_version,
        depth,
        transition_order,
        work: 0,
        budget_exhausted: false,
        nodes: vec![],
    };
    let root = index.index_term(index.property(), depth);
    append_trace(
        &mut trace,
        index,
        types,
        work_limit,
        evaluate,
        plan,
        None,
        TraceStep::child(root, TraceReason::PropertyViolation),
    );
    trace
}

/// Continue a grounded obligation using the same partial evaluation, witness,
/// Boolean and array traversal as the property. The caller supplies a valid
/// binder instance as provenance, not an assumed truth for the new body.
#[allow(clippy::too_many_arguments)]
pub(crate) fn append_trace(
    trace: &mut CountermodelTrace,
    index: &TransitionIndex,
    types: &[(String, String)],
    work_limit: usize,
    mut evaluate: impl FnMut(&Term) -> anyhow::Result<ModelEvaluation>,
    plan: Option<&QuantifierPlan>,
    parent: Option<usize>,
    step: TraceStep,
) {
    let mut cx = TraceContext {
        index,
        types,
        evaluate: &mut evaluate,
        remaining: work_limit.saturating_sub(trace.work),
        initializers: plan
            .map(|plan| InitializerSearch::new(plan, index.index_term(index.initial(), 0))),
        transitions: plan
            .map(|plan| TransitionSearch::new(plan, trace.depth, trace.transition_order)),
    };
    let mut queue = VecDeque::from([(parent, step)]);
    while let Some((parent, mut step)) = queue.pop_front() {
        let id = trace.nodes.len();
        let mut node = TraceNode {
            id,
            parent,
            expression: step.term.clone(),
            model_value: None,
            reason: step.reason.clone(),
            conditions: std::mem::take(&mut step.conditions),
            lemma: step.lemma.take(),
            status: TraceStatus::Expanded,
        };
        let mut ancestor = parent;
        while let Some(i) = ancestor {
            if trace.nodes[i].expression == node.expression {
                node.status = TraceStatus::Cycle;
                break;
            }
            ancestor = trace.nodes[i].parent;
        }
        let result = (|| {
            cx.charge()?;
            if let Some(frontier) = step.frontier.take() {
                return Err(frontier);
            }
            if node.status == TraceStatus::Cycle {
                return Ok(vec![]);
            }
            if let TraceReason::UnresolvedInitialization { expression, .. }
            | TraceReason::QuantifiedTransition {
                unresolved: Some(expression),
                ..
            } = &node.reason
            {
                node.status = TraceStatus::Undetermined {
                    expression: expression.clone(),
                };
                return Ok(vec![]);
            }
            let value = cx.observe(&node.expression)?.value;
            node.model_value = Some(value.clone());
            if parent.is_none() && value != "false" {
                node.status = TraceStatus::Unsupported {
                    detail: "property is not false in this model".into(),
                };
                return Ok(vec![]);
            }
            if let Some(lemma) = &mut node.lemma {
                lemma.model_value = Some(cx.boolean(&lemma.formula)?.value);
                if lemma.model_value.as_deref() == Some("false") {
                    node.status = if matches!(
                        node.reason,
                        TraceReason::Initialization { .. }
                            | TraceReason::QuantifiedTransition { .. }
                            | TraceReason::QuantifierWitness
                            | TraceReason::QuantifierMatch { .. }
                    ) {
                        TraceStatus::ViolatedQuantifierInstance
                    } else {
                        TraceStatus::ViolatedArrayAxiom
                    };
                    return Ok(vec![]);
                }
            }
            if matches!(
                node.reason,
                TraceReason::Transition { .. }
                    | TraceReason::ArrayAxiom
                    | TraceReason::Definition
                    | TraceReason::Conditional
                    | TraceReason::Initialization { .. }
                    | TraceReason::QuantifiedTransition { .. }
                    | TraceReason::QuantifierWitness
                    | TraceReason::AssertedQuantifierBody
            ) && parent.is_some_and(|p| trace.nodes[p].model_value.as_ref() != Some(&value))
            {
                node.status = TraceStatus::InconsistentStep;
                return Ok(vec![]);
            }
            expand(&mut cx, &mut node, plan)
        })();
        match result {
            Ok(children) => queue.extend(children.into_iter().map(|child| (Some(id), child))),
            Err(TraceError::Budget) => {
                node.status = TraceStatus::BudgetExhausted;
                trace.budget_exhausted = true;
            }
            Err(TraceError::Undetermined(expression)) => {
                node.status = TraceStatus::Undetermined { expression };
            }
            Err(TraceError::Evaluation(detail)) => {
                node.status = TraceStatus::EvaluationFailed { detail }
            }
        }
        trace.nodes.push(node);
        if trace.budget_exhausted {
            break;
        }
    }
    trace.work = work_limit - cx.remaining;
}

fn transition_steps(
    term: &Term,
    cx: &mut TraceContext<'_>,
    current: bool,
) -> Result<Vec<TraceStep>, TraceError> {
    let Some(mut search) = cx.transitions.take() else {
        return Ok(vec![]);
    };
    let result = search.steps(term, cx, current);
    cx.transitions = Some(search);
    result
}

fn expand(
    cx: &mut TraceContext<'_>,
    node: &mut TraceNode,
    plan: Option<&QuantifierPlan>,
) -> Result<Vec<TraceStep>, TraceError> {
    use crate::theories::array::countermodel::{is_read, read_step, ReadOutcome};
    let term = &node.expression;
    if let Some(expanded) = cx.index.expand_framed_leaf(term) {
        return Ok(vec![TraceStep::child(expanded, TraceReason::Definition)]);
    }
    if let Term::Attributes { term, .. } = term {
        return Ok(vec![TraceStep::child(
            *term.clone(),
            TraceReason::Definition,
        )]);
    }
    if is_read(term, cx.types) {
        // Current-frame equations may constrain a temporary relation without
        // assigning its next-state variable. Policy chooses their precedence.
        let current_first = cx.transitions.as_ref().is_some_and(|s| s.current_first());
        if current_first {
            let children = transition_steps(term, cx, true)?;
            if !children.is_empty() {
                return Ok(children);
            }
        }
        match read_step(term, cx)? {
            ReadOutcome::Step(step) => return Ok(vec![*step]),
            ReadOutcome::Branches(steps) => return Ok(steps),
            ReadOutcome::Stop(status) => node.status = status,
        }
        if matches!(node.status, TraceStatus::InitialState { .. }) {
            if let Some(mut search) = cx.initializers.take() {
                let result = search.steps(term, cx);
                cx.initializers = Some(search);
                let children = result?;
                if !children.is_empty() {
                    node.status = TraceStatus::Expanded;
                    return Ok(children);
                }
            }
        }
        if matches!(node.status, TraceStatus::Unsupported { .. }) {
            let children = transition_steps(term, cx, false)?;
            if !children.is_empty() {
                node.status = TraceStatus::Expanded;
                return Ok(children);
            }
        }
        if !current_first {
            let children = transition_steps(term, cx, true)?;
            if !children.is_empty() {
                node.status = TraceStatus::Expanded;
                return Ok(children);
            }
        }
        return Ok(vec![]);
    }
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        node.status = match term {
            Term::Constant(_) | Term::QualIdentifier(_) => TraceStatus::Value,
            _ => TraceStatus::Unsupported {
                detail: "binder or unexpanded term requires another analysis".into(),
            },
        };
        return Ok(vec![]);
    };
    let name = qual_identifier.get_name();
    let truth = node.model_value.as_deref() == Some("true");
    let mut children = Vec::new();
    match (name.as_str(), arguments.as_slice()) {
        ("not", [inner]) => children.push(TraceStep::child(
            inner.clone(),
            TraceReason::BooleanBranch {
                alternatives: false,
            },
        )),
        ("and" | "or", args) => {
            let alternatives = (name == "and") != truth;
            for arg in args {
                let observation = match cx.boolean(arg) {
                    Ok(value) => Some(value),
                    // Preserve this frontier without losing known siblings.
                    Err(TraceError::Undetermined(_)) => None,
                    Err(error) => return Err(error),
                };
                if observation
                    .as_ref()
                    .is_none_or(|o| !alternatives || (o.value == "true") == truth)
                {
                    children.push(TraceStep::child(
                        arg.clone(),
                        TraceReason::BooleanBranch { alternatives },
                    ));
                }
            }
        }
        ("=>", [left, right]) => {
            for (arg, desired) in [(left, false), (right, true)] {
                let observation = match cx.boolean(arg) {
                    Ok(value) => Some(value),
                    Err(TraceError::Undetermined(_)) => None,
                    Err(error) => return Err(error),
                };
                if observation
                    .as_ref()
                    .is_none_or(|o| !truth || (o.value == "true") == desired)
                {
                    children.push(TraceStep::child(
                        arg.clone(),
                        TraceReason::BooleanBranch {
                            alternatives: truth,
                        },
                    ));
                }
            }
        }
        ("ite", [condition, yes, no]) => {
            let observation = cx.boolean(condition)?;
            let branch = if observation.value == "true" { yes } else { no };
            children.push(TraceStep {
                frontier: None,
                term: branch.clone(),
                reason: TraceReason::Conditional,
                conditions: vec![observation],
                lemma: None,
            });
        }
        _ => {
            // Opaque applications are explicit frontiers: in particular, do not
            // rewrite a witness's captured arrays as though it were an array read.
            if !matches!(
                name.as_str(),
                "=" | "distinct" | "+" | "-" | "*" | "<" | ">" | "<=" | ">="
            ) {
                if matches!(node.model_value.as_deref(), Some("true" | "false")) {
                    if let Some(plan) = plan {
                        if let Some(step) =
                            crate::theories::quantifiers::countermodel::witness_step(
                                plan, node, cx,
                            )?
                        {
                            return Ok(vec![step]);
                        }
                    }
                }
                node.status = TraceStatus::Unsupported {
                    detail: format!("opaque application {name}"),
                };
                return Ok(vec![]);
            }
            for (index, arg) in arguments.iter().enumerate() {
                cx.charge()?;
                children.push(TraceStep::child(
                    arg.clone(),
                    TraceReason::Argument { index },
                ));
            }
        }
    }
    if children.is_empty() {
        node.status = TraceStatus::Value;
    }
    Ok(children)
}

mod term_text {
    use super::*;
    pub fn serialize<S: serde::Serializer>(term: &Term, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&term.to_string())
    }
    pub fn deserialize<'de, D: serde::Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Term, D::Error> {
        String::deserialize(deserializer)?
            .parse()
            .map_err(serde::de::Error::custom)
    }
}

#[cfg(test)]
mod tests;

mod requirements;
