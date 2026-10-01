//! Coordinator-owned symbolic work surviving changes to the solver model.
//! Source control flow is a search hint. Only binder and array theory instances
//! enter the candidate pool; model equalities and source assignments never do.
use crate::{
    policy::{effort::WorkAllowance, term_selection::TermCostFactory},
    problem_context::ProblemContext,
    rule_matching::{
        candidate::{InstantiationBatch, SymbolicInstance},
        provenance::CountermodelOrigin,
        search_context::{SearchContext, SearchFormulas},
    },
    theories::{
        array::obligations::transport,
        quantifiers::{dependency_search::Goal, equations::QuantifiedEquations, QuantifierPlan},
    },
    transition_index::TransitionIndex,
};
use smt2parser::concrete::Term;
use std::collections::{HashMap, HashSet, VecDeque};
mod agenda;
#[cfg(test)]
mod pool_tests;
use agenda::Agenda;

pub(crate) struct ObligationDiscovery {
    pub work: usize,
    pub pending: usize,
    pub demands: usize,
    pub contexts: usize,
}

#[derive(Default)]
pub(crate) struct RefinementObligations {
    depth: Option<u16>,
    agendas: Vec<Agenda>,
    active: Option<(u64, usize)>,
    pool: crate::rule_matching::symbolic_pool::SymbolicCandidatePool,
}

impl RefinementObligations {
    fn prepare_depth(&mut self, depth: u16) {
        if self.depth != Some(depth) {
            *self = Self {
                depth: Some(depth),
                ..Self::default()
            };
        }
    }

    pub(crate) fn remember_traced(
        &mut self,
        depth: u16,
        instances: impl IntoIterator<Item = (SymbolicInstance, CountermodelOrigin)>,
    ) -> usize {
        self.prepare_depth(depth);
        let mut count = 0;
        for (instance, origin) in instances {
            self.pool.remember_traced(instance, origin);
            count += 1;
        }
        count
    }

    pub(crate) fn remember(&mut self, instances: impl IntoIterator<Item = SymbolicInstance>) {
        self.pool.remember(instances);
    }

    pub(crate) fn discover(
        &mut self,
        formulas: SearchFormulas<'_>,
        smt: &dyn ProblemContext,
        depth: u16,
        model: u64,
        allowance: &WorkAllowance,
    ) -> anyhow::Result<ObligationDiscovery> {
        let index = formulas
            .index
            .ok_or_else(|| anyhow::anyhow!("VMT obligation search requires a formula index"))?;
        let plan = formulas.quantifiers;
        self.prepare_depth(depth);
        let current = if let Some((previous, current)) = self.active.filter(|(m, _)| *m == model) {
            debug_assert_eq!(previous, model);
            current
        } else {
            let mut selected = None;
            for (i, agenda) in self.agendas.iter().enumerate().rev() {
                if agenda.valid_for(|term| smt.eval_to_string(term))? {
                    selected = Some(i);
                    break;
                }
            }
            let current = if let Some(i) = selected {
                i
            } else {
                self.agendas.push(Agenda::new(plan, index, smt, depth)?);
                self.agendas.len() - 1
            };
            self.agendas[current].refresh(plan, smt);
            self.active = Some((model, current));
            current
        };
        let (instances, work) =
            self.agendas[current].advance(plan, index, smt, allowance.dependency_work)?;
        self.remember(instances);
        Ok(ObligationDiscovery {
            work,
            pending: self.agendas[current].pending(),
            demands: self.agendas[current].demands(),
            contexts: self.agendas.len(),
        })
    }

    pub(crate) fn candidates<F: TermCostFactory>(
        &mut self,
        context: &SearchContext<'_, F>,
    ) -> anyhow::Result<InstantiationBatch> {
        self.pool.candidates(context)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        policy::term_selection::array::ArrayAstSize,
        solver::SolverCheckResult,
        strategies::{Abstract, ProofStrategy, RefinementState},
        theories::quantifiers::refinement::QuantifierRefinement,
    };

    #[test]
    fn automatically_closes_captured_paxos_support_frame3() {
        close_captured_query(
            include_str!("../tests/fixtures/paxos-support-frame3.smt2"),
            3,
            false,
        );
    }

    #[test]
    fn automatically_closes_captured_paxos_guards_frame4() {
        close_captured_query(
            include_str!("../tests/fixtures/paxos-guards-frame4.smt2"),
            4,
            false,
        );
    }

    #[test]
    fn automatically_closes_captured_paxos_agreement_with_both_theories() {
        close_captured_query(
            include_str!("../tests/fixtures/paxos-agreement-frame1.smt2"),
            1,
            true,
        );
    }

    #[test]
    fn automatically_closes_captured_paxos_decide_frame2() {
        close_captured_query(
            include_str!("../tests/fixtures/paxos-decide-frame2.smt2"),
            2,
            false,
        );
    }

    #[test]
    fn automatically_closes_captured_paxos_updates_frame2() {
        close_captured_query(
            include_str!("../tests/fixtures/paxos-updates-frame2.smt2"),
            2,
            false,
        );
    }

    #[test]
    fn one_work_slices_match_a_large_slice_and_resume_on_an_equivalent_model() {
        let mut quantifiers = QuantifierRefinement::default();
        let model = quantifiers.configure_model(
            smt2parser::vmt::VMTModel::from_path(
                "examples/distributed_protocols/paxos/paxos.encoding.vmt",
            )
            .unwrap(),
            false,
        );
        let (model, types) = model.abstract_array_theory();
        let index = TransitionIndex::from_model(
            &model,
            &quantifiers
                .plan
                .rules
                .iter()
                .map(|r| r.name.clone())
                .collect(),
        );
        let commands = smt2parser::CommandStream::new(
            include_str!("../tests/fixtures/paxos-agreement-frame1.smt2").as_bytes(),
            smt2parser::concrete::SyntaxBuilder,
            None,
        )
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
        let problem = crate::smtlib_problem::SMTLIBProblem::from_commands(commands).unwrap();
        let strategy: Box<dyn ProofStrategy<'_, RefinementState>> =
            Box::new(Abstract::<ArrayAstSize>::new(
                2,
                false,
                crate::YardbirdPolicy::new(()),
                false,
            ));
        let mut smt =
            crate::smtlib_refinement_session::SmtlibRefinementSession::new_with_array_types(
                &problem,
                &strategy,
                crate::SolverBackend::Z3,
                false,
                types,
                None,
            )
            .unwrap();
        assert_eq!(smt.check_current_query(), SolverCheckResult::Sat);
        let mut large = RefinementObligations::default();
        let big = large
            .discover(
                SearchFormulas {
                    index: Some(&index),
                    quantifiers: &quantifiers.plan,
                },
                &smt,
                1,
                0,
                &WorkAllowance {
                    dependency_work: 4096,
                    ..Default::default()
                },
            )
            .unwrap();
        assert!(big.work > 1 && !large.pool.instances().is_empty());
        let mut sliced = RefinementObligations::default();
        let mut small = None;
        for work in 0..big.work {
            // Changing the model identity forces revalidation, even when the
            // actual model has identical branch choices.
            let report = sliced
                .discover(
                    SearchFormulas {
                        index: Some(&index),
                        quantifiers: &quantifiers.plan,
                    },
                    &smt,
                    1,
                    (work / 64) as u64,
                    &WorkAllowance {
                        dependency_work: 1,
                        ..Default::default()
                    },
                )
                .unwrap();
            assert_eq!(report.work, 1);
            assert_eq!(
                report.contexts, 1,
                "equivalent model must resume existing work"
            );
            small = Some(report);
        }
        let agenda = &sliced.agendas[0];
        assert!(agenda.valid_for(|t| smt.eval_to_string(t)).unwrap());
        assert!(
            !agenda
                .valid_for(|t| {
                    Ok(match smt.eval_to_string(t)?.trim() {
                        "true" => "false".to_owned(),
                        "false" => "true".to_owned(),
                        other => other.to_owned(),
                    })
                })
                .unwrap(),
            "changed model decisions must deactivate the saved context"
        );
        let small = small.unwrap();
        assert_eq!((small.pending, small.demands), (big.pending, big.demands));
        assert_eq!(
            sliced
                .pool
                .instances()
                .iter()
                .map(|i| &i.term)
                .collect::<Vec<_>>(),
            large
                .pool
                .instances()
                .iter()
                .map(|i| &i.term)
                .collect::<Vec<_>>()
        );
    }

    fn close_captured_query(source: &str, depth: u16, require_transport: bool) {
        let mut quantifiers = QuantifierRefinement::default();
        let model = quantifiers.configure_model(
            smt2parser::vmt::VMTModel::from_path(
                "examples/distributed_protocols/paxos/paxos.encoding.vmt",
            )
            .unwrap(),
            false,
        );
        let (model, types) = model.abstract_array_theory();
        let index = TransitionIndex::from_model(
            &model,
            &quantifiers
                .plan
                .rules
                .iter()
                .map(|r| r.name.clone())
                .collect(),
        );
        let mut commands = smt2parser::CommandStream::new(
            source.as_bytes(),
            smt2parser::concrete::SyntaxBuilder,
            None,
        )
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
        let strategy: Box<dyn ProofStrategy<'_, RefinementState>> =
            Box::new(Abstract::<ArrayAstSize>::new(
                2,
                false,
                crate::YardbirdPolicy::new(()),
                false,
            ));
        let mut obligations = RefinementObligations::default();
        let mut arrays = 0;
        let mut binders = 0;
        let mut satisfied = HashSet::new();
        let mut reused_satisfied = false;
        for round in 0..40 {
            let problem =
                crate::smtlib_problem::SMTLIBProblem::from_commands(commands.clone()).unwrap();
            let mut smt =
                crate::smtlib_refinement_session::SmtlibRefinementSession::new_with_array_types(
                    &problem,
                    &strategy,
                    crate::SolverBackend::Z3,
                    false,
                    types.clone(),
                    None,
                )
                .unwrap();
            if smt.check_current_query() == SolverCheckResult::Unsat {
                assert!(round > 0 && binders > 0);
                assert!(!require_transport || arrays > 0);
                assert!(
                    !require_transport || reused_satisfied,
                    "a previously satisfied link must survive model changes"
                );
                eprintln!("automatic frame-{depth} closure: {round} rounds, {arrays} array instances, {binders} binder instances");
                return;
            }
            let allowance = WorkAllowance::default();
            for slice in 0..10_000 {
                let discovery = obligations
                    .discover(
                        SearchFormulas {
                            index: Some(&index),
                            quantifiers: &quantifiers.plan,
                        },
                        &smt,
                        depth,
                        round,
                        &allowance,
                    )
                    .unwrap();
                let violated = obligations
                    .pool
                    .instances()
                    .iter()
                    .any(|i| smt.eval_to_string(&i.term).unwrap().trim() == "false");
                if violated || discovery.pending == 0 {
                    break;
                }
                assert!(slice < 9_999, "symbolic closure did not quiesce");
            }
            let mut added = 0;
            for instance in obligations.pool.instances() {
                if smt.eval_to_string(&instance.term).unwrap().trim() == "false" {
                    reused_satisfied |= satisfied.contains(&instance.term);
                    match instance.rule.category() {
                        crate::rule_matching::rule::QuantifiedRuleCategory::ArrayAxiom => {
                            arrays += 1
                        }
                        _ => binders += 1,
                    }
                    commands.push(smt2parser::concrete::Command::Assert {
                        term: instance.term.clone(),
                    });
                    added += 1;
                } else {
                    satisfied.insert(instance.term.clone());
                }
            }
            assert!(
                added > 0,
                "stalled round {round}, retained {} instances",
                obligations.pool.instances().len()
            );
        }
        panic!("captured query did not close");
    }
}
