//! Model-local continuation of read frontiers left by guidance. The equation
//! matcher supplies exact captures and whatever bindings the demand determines;
//! ordinary binder search validates and completes the resulting requests.
use super::{
    clauses::source_helpers,
    equations::{EquationCompiler, EquationCursor, QuantifiedEquations},
    refinement::DependencyWork,
    QuantifierPlan,
};
use crate::{
    countermodel::{CountermodelTrace, TraceStatus},
    problem_context::ProblemContext,
    rule_matching::provenance::CountermodelOrigin,
};
use smt2parser::concrete::Term;
use std::collections::VecDeque;

pub(super) struct TracedEquationSearch {
    frontiers: Vec<(Term, CountermodelOrigin)>,
    sources: VecDeque<Term>,
    compiler: Option<EquationCompiler>,
    equations: Option<QuantifiedEquations>,
    jobs: VecDeque<(usize, EquationCursor)>,
}

impl TracedEquationSearch {
    pub fn new(trace: &CountermodelTrace, plan: &QuantifierPlan, smt: &dyn ProblemContext) -> Self {
        let frontiers = trace.nodes.iter().filter(|node| {
            matches!(node.status, TraceStatus::Unsupported { .. } | TraceStatus::Undetermined { .. } | TraceStatus::BudgetExhausted)
                && matches!(&node.expression, Term::Application { qual_identifier, .. } if qual_identifier.get_name().starts_with("Read_"))
        }).map(|node| (node.expression.clone(), CountermodelOrigin {
            model_version: trace.model_version, depth: trace.depth, node: node.id,
        })).collect::<Vec<_>>();
        let mut sources = if frontiers.is_empty() {
            vec![]
        } else {
            source_helpers(plan, smt)
        };
        sources.sort_by_key(ToString::to_string);
        Self {
            frontiers,
            sources: sources.into(),
            compiler: None,
            equations: None,
            jobs: VecDeque::new(),
        }
    }

    pub fn pending(&self) -> bool {
        self.compiler.is_some() || !self.sources.is_empty() || !self.jobs.is_empty()
    }

    pub fn advance(
        &mut self,
        plan: &QuantifierPlan,
        limit: usize,
        output: &mut Vec<DependencyWork>,
    ) -> usize {
        let mut work = 0;
        while work < limit && self.pending() {
            work += 1;
            if let Some((frontier, mut cursor)) = self.jobs.pop_front() {
                let (term, origin) = &self.frontiers[frontier];
                let mut requests = Vec::new();
                cursor.step_requests(self.equations.as_ref().unwrap(), term, plan, &mut requests);
                for request in requests {
                    if let Some(existing) = output.iter_mut().find(|old| old.request == request) {
                        existing.origin.get_or_insert_with(|| origin.clone());
                    } else {
                        output.push(DependencyWork {
                            description: format!(
                                "countermodel node {}: {} {:?} {:?}",
                                origin.node, request.helper, request.phase, request.bindings
                            ),
                            request,
                            origin: Some(origin.clone()),
                        });
                    }
                }
                if cursor.pending() {
                    self.jobs.push_back((frontier, cursor));
                }
            } else if let Some(compiler) = &mut self.compiler {
                compiler.step(plan);
                if !compiler.pending() {
                    let equations = self.compiler.take().unwrap().finish();
                    if !equations.is_empty() {
                        self.jobs.extend(
                            (0..self.frontiers.len()).map(|i| (i, EquationCursor::default())),
                        );
                    }
                    self.equations = Some(equations);
                }
            } else if let Some(source) = self.sources.pop_front() {
                self.compiler = Some(EquationCompiler::new(source));
            }
        }
        work
    }
}
