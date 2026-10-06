//! One counter-model-selected read step. Unlike broad obligation transport,
//! this records the actual branch and its assumptions without asserting them.
use crate::{
    countermodel::{TraceContext, TraceError, TraceLemma, TraceReason, TraceStatus, TraceStep},
    theories::quantifiers::app,
    transition_index::leaf_symbol,
};
use smt2parser::concrete::Term;
use std::collections::{HashSet, VecDeque};

pub(crate) enum ReadOutcome {
    Step(Box<TraceStep>),
    Branches(Vec<TraceStep>),
    Stop(TraceStatus),
}

impl ReadOutcome {
    fn step(step: TraceStep) -> Self {
        Self::Step(Box::new(step))
    }
}

pub(crate) fn is_read(term: &Term, types: &[(String, String)]) -> bool {
    matches!(term, Term::Application { qual_identifier, arguments } if arguments.len() == 2 && types.iter().any(|(i,v)| qual_identifier.get_name() == format!("Read_{i}_{v}")))
}

pub(crate) fn read_step(term: &Term, cx: &mut TraceContext<'_>) -> Result<ReadOutcome, TraceError> {
    cx.charge()?;
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        unreachable!()
    };
    let [array, index] = arguments.as_slice() else {
        unreachable!()
    };
    let name = qual_identifier.get_name();
    if let Term::Application {
        qual_identifier: head,
        arguments: args,
    } = array
    {
        let (is, vs) = cx
            .types
            .iter()
            .find(|(i, v)| name == format!("Read_{i}_{v}"))
            .expect("typed read");
        let mut conditions = vec![];
        let choice = if head.get_name() == format!("Write_{is}_{vs}") {
            if let [base, at, value] = args.as_slice() {
                let equal = cx.boolean(&app("=", vec![at.clone(), index.clone()]))?;
                let same = equal.value == "true";
                conditions.push(equal);
                Some((
                    if same {
                        value.clone()
                    } else {
                        app(&name, vec![base.clone(), index.clone()])
                    },
                    usize::from(!same),
                ))
            } else {
                None
            }
        } else if head.get_name() == format!("ConstArr_{is}_{vs}") {
            args.first()
                .filter(|_| args.len() == 1)
                .map(|value| (value.clone(), 0))
        } else {
            None
        };
        if let Some((replacement, selected)) = choice {
            let mut instances = vec![];
            super::obligations::read_alternatives(term, cx.types, &mut instances);
            let instance = instances
                .into_iter()
                .nth(selected)
                .expect("matching array axiom");
            return Ok(ReadOutcome::step(TraceStep {
                frontier: None,
                term: replacement,
                reason: TraceReason::ArrayAxiom,
                conditions,
                lemma: Some(TraceLemma {
                    instance: Some(instance.clone()),
                    rule: instance.rule.name().to_owned(),
                    formula: instance.term,
                    model_value: None,
                }),
            }));
        }
    }
    match array_step(array, cx)? {
        ReadOutcome::Step(mut step) => {
            step.term = app(&name, vec![step.term, index.clone()]);
            Ok(ReadOutcome::Step(step))
        }
        ReadOutcome::Branches(mut steps) => {
            for step in &mut steps {
                step.term = app(&name, vec![step.term.clone(), index.clone()]);
            }
            Ok(ReadOutcome::Branches(steps))
        }
        stop => Ok(stop),
    }
}

fn array_step(array: &Term, cx: &mut TraceContext<'_>) -> Result<ReadOutcome, TraceError> {
    cx.charge()?;
    if let Some(expanded) = cx.index.expand_framed_leaf(array) {
        return Ok(ReadOutcome::step(TraceStep {
            frontier: None,
            term: expanded,
            reason: TraceReason::Definition,
            conditions: vec![],
            lemma: None,
        }));
    }
    if is_read(array, cx.types) {
        return read_step(array, cx);
    }
    if let Term::Application {
        qual_identifier,
        arguments,
    } = array
    {
        if qual_identifier.get_name() == "ite" {
            if let [condition, yes, no] = arguments.as_slice() {
                let observation = cx.boolean(condition)?;
                return Ok(ReadOutcome::step(TraceStep {
                    frontier: None,
                    term: if observation.value == "true" { yes } else { no }.clone(),
                    reason: TraceReason::Conditional,
                    conditions: vec![observation],
                    lemma: None,
                }));
            }
        }
    }
    if let Some((name, frame)) =
        leaf_symbol(array).and_then(|s| smt2parser::vmt::split_framed_symbol(&s))
    {
        if let Ok(frame) = u16::try_from(frame) {
            if frame == 0 {
                let steps = initial_steps(array, cx)?;
                if !steps.is_empty() {
                    return Ok(ReadOutcome::Branches(steps));
                }
                return Ok(ReadOutcome::Stop(TraceStatus::InitialState {
                    array: array.to_string(),
                }));
            }
            let previous = frame - 1;
            let mut selected = None;
            for path in cx.index.update_paths(&name) {
                cx.charge()?;
                let mut conditions = vec![];
                let mut enabled = true;
                for guard in &path.guards {
                    let term = cx.index.index_term(&guard.expression, previous);
                    let observation = cx.boolean(&term)?;
                    enabled &= (observation.value == "true") == guard.required_value;
                    conditions.push(observation);
                    if !enabled {
                        break;
                    }
                }
                if !enabled {
                    continue;
                }
                if selected.is_some() {
                    return Ok(ReadOutcome::Stop(TraceStatus::Unsupported {
                        detail: format!("multiple enabled updates for {array}"),
                    }));
                }
                selected = Some(TraceStep {
                    frontier: None,
                    term: cx.index.index_term(&path.value, previous),
                    reason: TraceReason::Transition {
                        frame: previous,
                        action: path.action.clone(),
                        assignment: app(
                            "=",
                            vec![
                                cx.index.index_term(&path.target_expression, previous),
                                cx.index.index_term(&path.value, previous),
                            ],
                        ),
                    },
                    conditions,
                    lemma: None,
                });
            }
            if let Some(step) = selected {
                return Ok(ReadOutcome::step(step));
            }
        }
    }
    Ok(ReadOutcome::Stop(TraceStatus::Unsupported {
        detail: format!("no supported predecessor for array {array}"),
    }))
}

/// Follow every available source-backed initial path within the shared budget.
/// Unknown/error paths become independent frontiers; they cannot hide another
/// initializer. A local visited set bounds alias cycles, including when no
/// functional initializer is reachable and quantified initialization must run.
fn initial_steps(array: &Term, cx: &mut TraceContext<'_>) -> Result<Vec<TraceStep>, TraceError> {
    let mut pending = VecDeque::from([(array.clone(), vec![])]);
    let mut seen = HashSet::from([array.clone()]);
    let mut steps = Vec::new();
    while let Some((array, conditions)) = pending.pop_front() {
        cx.charge()?;
        let Some(symbol) = leaf_symbol(&array) else {
            continue;
        };
        for path in cx.index.initial_equalities(&symbol) {
            cx.charge()?;
            let mut observations = conditions.clone();
            let enabled = (|| {
                for guard in &path.guards {
                    let observation = cx.boolean(&guard.expression)?;
                    let active = (observation.value == "true") == guard.required_value;
                    observations.push(observation);
                    if !active {
                        return Ok(false);
                    }
                }
                let equality = cx.boolean(&path.equality)?;
                let active = equality.value == "true";
                observations.push(equality);
                Ok(active)
            })();
            let frontier = match enabled {
                Ok(false) => continue,
                Ok(true) if leaf_symbol(&path.value).is_some() => {
                    if seen.insert(path.value.clone()) {
                        pending.push_back((path.value.clone(), observations));
                    }
                    continue;
                }
                Ok(true) => None,
                Err(TraceError::Budget) => return Err(TraceError::Budget),
                Err(error) => Some(error),
            };
            steps.push(TraceStep {
                term: path.value.clone(),
                reason: TraceReason::Initialization { path: vec![] },
                conditions: observations,
                lemma: None,
                frontier,
            });
        }
    }
    Ok(steps)
}
