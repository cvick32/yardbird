//! Read-only explanations of one counter-model. These observations are not proofs
//! or asserted equalities; the refinement policy remains independent of tracing.
use serde::{Deserialize, Serialize};
use smt2parser::concrete::Term;
use std::collections::VecDeque;

use crate::transition_index::TransitionIndex;

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
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TraceStatus {
    Expanded,
    Value,
    InitialState { array: String },
    Unsupported { detail: String },
    EvaluationFailed { detail: String },
    ViolatedArrayAxiom,
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
    pub work: usize,
    pub budget_exhausted: bool,
    pub nodes: Vec<TraceNode>,
}

pub(crate) enum TraceError {
    Budget,
    Evaluation(String),
}

/// Both traversal steps and model queries consume work. The caller owns the
/// model lifetime; no solver value is retained as a logical constraint.
pub(crate) struct TraceContext<'a> {
    pub index: &'a TransitionIndex,
    pub types: &'a [(String, String)],
    evaluate: &'a mut dyn FnMut(&Term) -> anyhow::Result<String>,
    remaining: usize,
}
impl TraceContext<'_> {
    pub fn charge(&mut self) -> Result<(), TraceError> {
        self.remaining = self.remaining.checked_sub(1).ok_or(TraceError::Budget)?;
        Ok(())
    }
    pub fn observe(&mut self, term: &Term) -> Result<Observation, TraceError> {
        self.charge()?;
        let value = (self.evaluate)(term).map_err(|e| TraceError::Evaluation(e.to_string()))?;
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
}
impl TraceStep {
    fn child(term: Term, reason: TraceReason) -> Self {
        Self {
            term,
            reason,
            conditions: vec![],
            lemma: None,
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
    mut evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
) -> CountermodelTrace {
    let mut cx = TraceContext {
        index,
        types,
        evaluate: &mut evaluate,
        remaining: work_limit,
    };
    let mut trace = CountermodelTrace {
        model_version,
        depth,
        work: 0,
        budget_exhausted: false,
        nodes: vec![],
    };
    let root = index.index_term(index.property(), depth);
    let mut queue =
        VecDeque::from([(None, TraceStep::child(root, TraceReason::PropertyViolation))]);
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
            if node.status == TraceStatus::Cycle {
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
                    node.status = TraceStatus::ViolatedArrayAxiom;
                    return Ok(vec![]);
                }
            }
            if matches!(
                node.reason,
                TraceReason::Transition { .. }
                    | TraceReason::ArrayAxiom
                    | TraceReason::Definition
                    | TraceReason::Conditional
            ) && parent.is_some_and(|p| trace.nodes[p].model_value.as_ref() != Some(&value))
            {
                node.status = TraceStatus::InconsistentStep;
                return Ok(vec![]);
            }
            expand(&mut cx, &mut node)
        })();
        match result {
            Ok(children) => queue.extend(children.into_iter().map(|child| (Some(id), child))),
            Err(TraceError::Budget) => {
                node.status = TraceStatus::BudgetExhausted;
                trace.budget_exhausted = true;
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
    trace
}

fn expand(cx: &mut TraceContext<'_>, node: &mut TraceNode) -> Result<Vec<TraceStep>, TraceError> {
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
        return match read_step(term, cx)? {
            ReadOutcome::Step(step) => Ok(vec![*step]),
            ReadOutcome::Stop(status) => {
                node.status = status;
                Ok(vec![])
            }
        };
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
                let observation = cx.boolean(arg)?;
                if !alternatives || (observation.value == "true") == truth {
                    children.push(TraceStep::child(
                        arg.clone(),
                        TraceReason::BooleanBranch { alternatives },
                    ));
                }
            }
        }
        ("=>", [left, right]) => {
            let left_value = cx.boolean(left)?;
            let right_value = cx.boolean(right)?;
            if !truth || left_value.value == "false" {
                children.push(TraceStep::child(
                    left.clone(),
                    TraceReason::BooleanBranch {
                        alternatives: truth,
                    },
                ));
            }
            if !truth || right_value.value == "true" {
                children.push(TraceStep::child(
                    right.clone(),
                    TraceReason::BooleanBranch {
                        alternatives: truth,
                    },
                ));
            }
        }
        ("ite", [condition, yes, no]) => {
            let observation = cx.boolean(condition)?;
            let branch = if observation.value == "true" { yes } else { no };
            children.push(TraceStep {
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
