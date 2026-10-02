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

pub(crate) struct InitializerSearch<'a> {
    plan: &'a QuantifierPlan,
    root: Term,
    root_observation: Option<Observation>,
    compiler: Option<EquationCompiler>,
    equations: Option<QuantifiedEquations>,
}

impl<'a> InitializerSearch<'a> {
    pub(crate) fn new(plan: &'a QuantifierPlan, root: Term) -> Self {
        Self {
            plan,
            compiler: Some(EquationCompiler::new(root.clone())),
            root,
            root_observation: None,
            equations: None,
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
                    "initial condition is not true in the counter-model".into(),
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
                            "inactive helper on an asserted initialization path".into(),
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
                reason: match unresolved {
                    Some(expression) => TraceReason::UnresolvedInitialization { path, expression },
                    None => TraceReason::Initialization { path },
                },
                conditions: vec![self.root_observation.as_ref().unwrap().clone()],
                lemma: frontier,
            });
        }
        Ok(children)
    }
}
