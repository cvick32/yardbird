//! Explain quantified helpers and initial reads, retaining each helper guard.
use super::{
    app,
    equations::{EquationCompiler, EquationCursor, QuantifiedEquations},
    substitute, BinderKind, QuantifierPlan,
};
use crate::countermodel::{
    Observation, TraceContext, TraceError, TraceLemma, TraceNode, TraceReason, TraceStep,
};
use crate::rule_matching::{candidate::SymbolicInstance, rule::QuantifiedRule};
use smt2parser::concrete::Term;

/// A false universal or true existential has a source-defined witness tuple.
/// Follow its body only after checking the active witness implication. Other
/// polarities require a binding search, not an arbitrary witness substitution.
pub(crate) fn witness_step(
    plan: &QuantifierPlan,
    node: &TraceNode,
    cx: &mut TraceContext<'_>,
) -> Result<Option<TraceStep>, TraceError> {
    let Term::Application {
        qual_identifier,
        arguments,
    } = &node.expression
    else {
        return Ok(None);
    };
    for rule in &plan.rules {
        cx.charge()?;
        if rule.name != qual_identifier.get_name() {
            continue;
        }
        if !matches!(
            (rule.kind, node.model_value.as_deref()),
            (BinderKind::Forall, Some("false")) | (BinderKind::Exists, Some("true"))
        ) {
            return Ok(None);
        }
        if arguments.len() != rule.captures.len() {
            return Err(TraceError::Evaluation(
                "quantifier capture arity mismatch".into(),
            ));
        }
        let values = rule
            .witnesses
            .iter()
            .map(|name| app(name, arguments.clone()))
            .collect::<Vec<_>>();
        let bindings = rule
            .captures
            .iter()
            .chain(&rule.variables)
            .map(|(symbol, _)| symbol.clone())
            .zip(arguments.iter().chain(&values).cloned())
            .collect::<Vec<_>>();
        let body = substitute(rule.body.clone(), bindings.clone());
        let instance = SymbolicInstance {
            rule: QuantifiedRule::input_binder(&rule.name),
            term: rule
                .witness_instance(arguments)
                .expect("Boolean binder has witnesses"),
            bindings: bindings
                .into_iter()
                .map(|(symbol, term)| (symbol.0, term))
                .collect(),
        };
        let value = match cx.boolean(&instance.term) {
            Ok(observation) => Some(observation.value),
            Err(TraceError::Undetermined(_)) => None,
            Err(error) => return Err(error),
        };
        return Ok(Some(TraceStep {
            term: if value.as_deref() == Some("true") {
                body
            } else {
                instance.term.clone()
            },
            reason: TraceReason::QuantifierWitness,
            conditions: vec![Observation {
                expression: node.expression.clone(),
                value: node.model_value.clone().expect("known binder truth"),
            }],
            lemma: Some(TraceLemma {
                rule: instance.rule.name().to_owned(),
                formula: instance.term.clone(),
                model_value: value,
                instance: Some(instance),
            }),
        }));
    }
    Ok(None)
}

pub(crate) struct EquationSearch<'a> {
    plan: &'a QuantifierPlan,
    root: Term,
    root_observation: Option<Observation>,
    compiler: Option<EquationCompiler>,
    equations: Option<QuantifiedEquations>,
    transition_frame: Option<u16>,
    conditions: Vec<Observation>,
}

impl<'a> EquationSearch<'a> {
    pub(crate) fn new(plan: &'a QuantifierPlan, root: Term) -> Self {
        Self {
            plan,
            compiler: Some(EquationCompiler::new(root.clone())),
            root,
            root_observation: None,
            equations: None,
            transition_frame: None,
            conditions: Vec::new(),
        }
    }

    pub(crate) fn steps(
        &mut self,
        read: &Term,
        cx: &mut TraceContext<'_>,
    ) -> Result<Vec<TraceStep>, TraceError> {
        if self.root_observation.is_none() {
            let root = cx.boolean(&self.root)?;
            if root.value != "true" {
                return Err(TraceError::Evaluation(
                    "equation root is not true in the counter-model".into(),
                ));
            }
            self.root_observation = Some(root);
        }
        if let Some(compiler) = &mut self.compiler {
            while compiler.pending() {
                cx.charge()?;
                compiler.step_with_definitions(self.plan, Some(cx.index));
            }
            self.equations = Some(self.compiler.take().unwrap().finish());
        }
        let equations = self.equations.as_ref().unwrap();
        let mut cursor = EquationCursor::default();
        let mut children = Vec::new();
        while cursor.pending() {
            cx.charge()?;
            let mut instances = Vec::new();
            let Some(replacement) = cursor.step(equations, read, self.plan, &mut instances) else {
                continue;
            };
            let mut path = Vec::new();
            let mut frontier = None;
            let mut unresolved = None;
            for instance in instances {
                // A satisfied implication with a false helper is not permission
                // to use its body as an equation. Walk only the active chain.
                let Term::Application { arguments, .. } = &instance.term else {
                    unreachable!()
                };
                let evaluation = (|| {
                    if cx.boolean(&arguments[0])?.value != "true" {
                        return Err(TraceError::Evaluation(
                            "inactive helper on an asserted equation path".into(),
                        ));
                    }
                    Ok(cx.boolean(&instance.term)?.value)
                })();
                let value = match evaluation {
                    Ok(value) => Some(value),
                    Err(TraceError::Undetermined(expression)) => {
                        unresolved = Some(expression);
                        None
                    }
                    Err(error) => return Err(error),
                };
                let lemma = TraceLemma {
                    rule: instance.rule.name().to_owned(),
                    formula: instance.term.clone(),
                    model_value: value.clone(),
                    instance: Some(instance),
                };
                if value.as_deref() == Some("false") || unresolved.is_some() {
                    frontier = Some(lemma);
                    break;
                }
                path.push(lemma);
            }
            children.push(TraceStep {
                term: frontier
                    .as_ref()
                    .map_or(replacement, |lemma| lemma.formula.clone()),
                reason: match (self.transition_frame, unresolved) {
                    (Some(frame), unresolved) => TraceReason::QuantifiedTransition {
                        frame,
                        path,
                        unresolved,
                    },
                    (None, Some(expression)) => {
                        TraceReason::UnresolvedInitialization { path, expression }
                    }
                    (None, None) => TraceReason::Initialization { path },
                },
                conditions: self
                    .conditions
                    .iter()
                    .cloned()
                    .chain(self.root_observation.iter().cloned())
                    .collect(),
                lemma: frontier,
            });
        }
        Ok(children)
    }
}

// Preserve the initializer entry point; both sources use the same guarded
// equation-chain validation and non-completing model evaluation.
pub(crate) type InitializerSearch<'a> = EquationSearch<'a>;

pub(crate) struct TransitionSearch<'a> {
    plan: &'a QuantifierPlan,
    sources: std::collections::HashMap<(Term, u16), Vec<EquationSearch<'a>>>,
    depth: u16,
    order: crate::policy::effort::GuidanceTransitionOrder,
}

impl<'a> TransitionSearch<'a> {
    pub fn new(
        plan: &'a QuantifierPlan,
        depth: u16,
        order: crate::policy::effort::GuidanceTransitionOrder,
    ) -> Self {
        Self {
            plan,
            depth,
            order,
            sources: Default::default(),
        }
    }

    pub fn current_first(&self) -> bool {
        self.order == crate::policy::effort::GuidanceTransitionOrder::CurrentFirst
    }

    pub fn steps(
        &mut self,
        read: &Term,
        cx: &mut TraceContext<'_>,
        current: bool,
    ) -> Result<Vec<TraceStep>, TraceError> {
        // Only peel array reads. A witness's captured array is not the array
        // being updated and must never determine the predecessor frame.
        let mut array = read;
        while crate::theories::array::countermodel::is_read(array, cx.types) {
            let Term::Application { arguments, .. } = array else {
                unreachable!()
            };
            array = &arguments[0];
        }
        let Some((_, frame)) = crate::transition_index::leaf_symbol(array)
            .and_then(|name| smt2parser::vmt::split_framed_symbol(&name))
        else {
            return Ok(vec![]);
        };
        let Ok(frame) = u16::try_from(frame) else {
            return Ok(vec![]);
        };
        let source_frame = if current {
            if self.order == crate::policy::effort::GuidanceTransitionOrder::PredecessorOnly
                || frame >= self.depth
            {
                return Ok(vec![]);
            }
            frame
        } else {
            let Some(previous) = frame.checked_sub(1) else {
                return Ok(vec![]);
            };
            previous
        };
        // Only transitions 0..depth are asserted. In particular, a current
        // equation at the final property frame must not become an explanation.
        if source_frame >= self.depth {
            return Ok(vec![]);
        }
        let key = (array.clone(), source_frame);
        if !self.sources.contains_key(&key) {
            let root = cx.index.index_term(cx.index.transition(), source_frame);
            let sources = active_equations(self.plan, root, array, source_frame, cx)?;
            self.sources.insert(key.clone(), sources);
        }
        let mut children = Vec::new();
        for source in self.sources.get_mut(&key).unwrap() {
            children.extend(source.steps(read, cx)?);
        }
        Ok(children)
    }
}

/// Traverse only model-true source branches. Binder bodies remain symbolic
/// until equation matching supplies the demanded read's exact tuple.
fn active_equations<'a>(
    plan: &'a QuantifierPlan,
    root: Term,
    array: &Term,
    frame: u16,
    cx: &mut TraceContext<'_>,
) -> Result<Vec<EquationSearch<'a>>, TraceError> {
    let mut queue = std::collections::VecDeque::from([(root, Vec::<Observation>::new())]);
    let mut result = Vec::new();
    while let Some((term, conditions)) = queue.pop_front() {
        cx.charge()?;
        if let Some(expanded) = cx.index.expand_framed_leaf(&term) {
            queue.push_back((expanded, conditions));
            continue;
        }
        if let Term::Attributes { term, .. } = term {
            queue.push_back((*term, conditions));
            continue;
        }
        let Term::Application {
            qual_identifier,
            arguments,
        } = &term
        else {
            continue;
        };
        match (qual_identifier.get_name().as_str(), arguments.as_slice()) {
            ("and", args) => queue.extend(args.iter().cloned().map(|t| (t, conditions.clone()))),
            ("=>", [guard, body]) => {
                let observed = cx.boolean(guard)?;
                if observed.value == "true" {
                    let mut conditions = conditions;
                    conditions.push(observed);
                    queue.push_back((body.clone(), conditions));
                }
            }
            ("ite", [guard, yes, no]) => {
                let observed = cx.boolean(guard)?;
                let branch = if observed.value == "true" { yes } else { no };
                let mut conditions = conditions;
                conditions.push(observed);
                queue.push_back((branch.clone(), conditions));
            }
            ("or", args) => {
                // Unknown alternatives cannot hide a known true branch.
                let mut unknown = None;
                let mut found = false;
                for arg in args {
                    let observed = match cx.boolean(arg) {
                        Ok(observed) => observed,
                        Err(TraceError::Undetermined(expression)) => {
                            unknown = Some(expression);
                            continue;
                        }
                        Err(error) => return Err(error),
                    };
                    if observed.value == "true" {
                        found = true;
                        let mut conditions = conditions.clone();
                        conditions.push(observed);
                        queue.push_back((arg.clone(), conditions));
                    }
                }
                if !found {
                    if let Some(expression) = unknown {
                        return Err(TraceError::Undetermined(expression));
                    }
                }
            }
            (name, _)
                if plan
                    .rules
                    .iter()
                    .any(|rule| rule.name == name && rule.kind == BinderKind::Forall)
                    && contains_term(&term, array) =>
            {
                let mut search = EquationSearch::new(plan, term);
                search.transition_frame = Some(frame);
                search.conditions = conditions;
                result.push(search);
            }
            _ => {}
        }
    }
    Ok(result)
}

fn contains_term(term: &Term, needle: &Term) -> bool {
    term == needle
        || match term {
            Term::Application { arguments, .. } => {
                arguments.iter().any(|arg| contains_term(arg, needle))
            }
            Term::Attributes { term, .. } => contains_term(term, needle),
            _ => false,
        }
}
