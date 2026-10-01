//! Match demanded initial reads to quantified equations, retaining each helper guard.
use super::{
    equations::{EquationCompiler, EquationCursor, QuantifiedEquations},
    QuantifierPlan,
};
use crate::countermodel::{
    Observation, TraceContext, TraceError, TraceLemma, TraceReason, TraceStep,
};
use smt2parser::concrete::Term;

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
