use std::mem;

use log::{info, trace};
use smt2parser::{
    concrete::Term,
    vmt::{quantified_instantiator::UnquantifiedInstantiator, VMTModel},
};

use crate::{
    cost_functions::YardbirdCostFunction,
    driver::{self},
    ic3ia::{call_ic3ia, ic3ia_output_contains_proof},
    solver_interface::SolverInterface,
    theories::array::{
        array_axioms::{
            expr_to_term, saturate_with_array_types, translate_term, ArrayExpr, ArrayLanguage,
        },
        array_conflict_scheduler::preprocess_array_expr,
    },
    theory_support::{ArrayTheorySupport, TheorySupport},
    training::{AbstractInstantiationRecord, DecisionRecord},
    ProofLoopResult,
};

use super::{ProofAction, ProofStrategy};

fn trace_conflicts_enabled() -> bool {
    log::log_enabled!(log::Level::Trace)
}

fn trace_instantiations_enabled() -> bool {
    log::log_enabled!(log::Level::Trace)
}

/// Global state carried across different BMC depths
pub struct Abstract<F>
where
    F: YardbirdCostFunction<ArrayLanguage>,
{
    const_instantiations: Vec<Term>,
    _bmc_depth: u16,
    run_ic3ia: bool,
    cost_fn_factory: fn(&dyn SolverInterface, u32) -> F,
    discovered_array_types: Vec<(String, String)>,
    decision_data: Vec<DecisionRecord>,
    abstract_instantiations: Vec<AbstractInstantiationRecord>,
}

impl<F> Abstract<F>
where
    F: YardbirdCostFunction<ArrayLanguage>,
{
    pub fn new(
        bmc_depth: u16,
        run_ic3ia: bool,
        cost_fn_factory: fn(&dyn SolverInterface, u32) -> F,
    ) -> Self {
        Self {
            _bmc_depth: bmc_depth,
            run_ic3ia,
            const_instantiations: vec![],
            cost_fn_factory,
            discovered_array_types: vec![],
            decision_data: vec![],
            abstract_instantiations: vec![],
        }
    }
}

/// State for the inner refinement looop
pub struct ArrayRefinementState {
    pub depth: u16,
    pub egraph: egg::EGraph<ArrayLanguage, ()>,
    pub instantiations: Vec<ArrayExpr>,
    pub const_instantiations: Vec<ArrayExpr>,
    pub array_types: Vec<(String, String)>,
}

impl ArrayRefinementState {
    pub fn update_with_subterms(
        &mut self,
        model: &z3::Model,
        smt: &dyn crate::solver_interface::SolverInterface,
    ) -> anyhow::Result<()> {
        for term in smt.get_all_subterms() {
            let z3_term = smt.rewrite_term(term);
            let model_interp = smt.get_interpretation(model, &z3_term);
            let interp_str = model_interp.to_string();
            let term_id = self.egraph.add_expr(&translate_term(term.clone()).unwrap());
            let preprocessed = preprocess_array_expr(&interp_str);
            let interp_id = self.egraph.add_expr(&preprocessed.parse()?);
            self.egraph.union(term_id, interp_id);
        }
        self.egraph.rebuild();
        Ok(())
    }
}

impl<F> ProofStrategy<'_, ArrayRefinementState> for Abstract<F>
where
    F: YardbirdCostFunction<ArrayLanguage> + 'static,
{
    fn get_theory_support(&self) -> Box<dyn TheorySupport> {
        Box::new(ArrayTheorySupport::new(self.discovered_array_types.clone()))
    }

    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        let (abstracted_model, discovered_types) = model.abstract_array_theory();
        self.discovered_array_types = discovered_types;
        abstracted_model
        //     .abstract_constants_over(self.bmc_depth)
    }

    fn setup(
        &mut self,
        smt: &dyn crate::solver_interface::SolverInterface,
        depth: u16,
    ) -> driver::Result<ArrayRefinementState> {
        let egraph = egg::EGraph::new(());
        // Use discovered_array_types if available (VMT mode via configure_model),
        // otherwise get from SolverInterface (SMTLIB mode)
        let array_types = if self.discovered_array_types.is_empty() {
            smt.get_array_types()
        } else {
            self.discovered_array_types.clone()
        };
        Ok(ArrayRefinementState {
            depth,
            egraph,
            instantiations: vec![],
            const_instantiations: vec![],
            array_types,
        })
    }

    fn unsat(
        &mut self,
        state: &mut ArrayRefinementState,
        _solver: &dyn crate::solver_interface::SolverInterface,
    ) -> driver::Result<ProofAction> {
        info!("RULED OUT ALL COUNTEREXAMPLES OF DEPTH {}", state.depth);
        Ok(ProofAction::NextDepth)
    }

    fn sat(
        &mut self,
        state: &mut ArrayRefinementState,
        smt: &dyn crate::solver_interface::SolverInterface,
        refinement_step: u32,
    ) -> driver::Result<ProofAction> {
        if trace_conflicts_enabled() {
            trace!(
                "[yardbird::conflict-trace] sat depth={} refinement_step={} eclasses_before={}",
                state.depth,
                refinement_step,
                state.egraph.number_of_classes()
            );
        }
        let model = match smt.get_model() {
            Some(model) => model,
            None => todo!("No Z3 model available for SAT instance"),
        };
        state.update_with_subterms(model, smt)?;
        let cost_fn = (self.cost_fn_factory)(smt, state.depth as u32);
        let (insts, const_insts, decisions, abstract_instantiations) = saturate_with_array_types(
            &mut state.egraph,
            cost_fn,
            refinement_step,
            state.depth,
            &state.array_types,
        );
        state.instantiations.extend_from_slice(&insts);
        state.const_instantiations.extend_from_slice(&const_insts);
        self.decision_data.extend(decisions);
        self.abstract_instantiations.extend(abstract_instantiations);
        if trace_conflicts_enabled() {
            trace!(
                "[yardbird::conflict-trace] sat depth={} refinement_step={} produced regular_insts={} const_insts={} total_regular={} total_const={}",
                state.depth,
                refinement_step,
                insts.len(),
                const_insts.len(),
                state.instantiations.len(),
                state.const_instantiations.len()
            );
        }
        Ok(ProofAction::Continue)
    }

    #[allow(clippy::unnecessary_fold)]
    fn finish(
        &mut self,
        state: ArrayRefinementState,
        smt: &mut dyn crate::solver_interface::SolverInterface,
    ) -> driver::Result<()> {
        let trace_instantiations = trace_instantiations_enabled();
        let const_pairs: Vec<(String, Term)> = state
            .const_instantiations
            .iter()
            .map(|inst| {
                (
                    crate::training::canonical_term_hash(inst),
                    expr_to_term(inst.clone()),
                )
            })
            .collect();
        let variables = smt.get_variables().to_vec();
        for (term_hash, term) in &const_pairs {
            if trace_instantiations {
                trace!(
                    "[yardbird::inst-trace] const abstract-hash={} abstract-term={}",
                    term_hash,
                    term
                );
            }
            if let Some(inst) =
                UnquantifiedInstantiator::rewrite_unquantified(term.clone(), variables.clone())
            {
                let abstract_id = self
                    .abstract_instantiations
                    .iter()
                    .find(|record| record.term_hash == *term_hash)
                    .map(|record| record.abstract_instantiation_id.clone());
                if trace_instantiations {
                    trace!(
                        "[yardbird::inst-trace] const concrete abstract-hash={} abstract-id={abstract_id:?} concrete-term={}",
                        term_hash,
                        inst
                    );
                }
                let added = smt.add_instantiation(inst, abstract_id);
                if trace_instantiations {
                    trace!(
                        "[yardbird::inst-trace] const add-result abstract-hash={} added={added}",
                        term_hash
                    );
                }
            } else if trace_instantiations {
                trace!(
                    "[yardbird::inst-trace] const rewrite-none abstract-hash={}",
                    term_hash
                );
            }
        }
        self.const_instantiations
            .extend(state.const_instantiations.into_iter().map(expr_to_term));

        let terms: Vec<(String, Term)> = state
            .instantiations
            .into_iter()
            .map(|inst| {
                let hash = crate::training::canonical_term_hash(&inst);
                (hash, expr_to_term(inst))
            })
            .collect();
        let variables = smt.get_variables().to_vec();
        let _ = terms
            .into_iter()
            .flat_map(|(term_hash, term)| {
                if trace_instantiations {
                    trace!(
                        "[yardbird::inst-trace] regular abstract-hash={} abstract-term={}",
                        term_hash, term
                    );
                }
                UnquantifiedInstantiator::rewrite_unquantified(term, variables.clone()).map(
                    move |inst| (term_hash.clone(), inst),
                )
            })
            .map(|(term_hash, inst)| {
                let abstract_id = self
                    .abstract_instantiations
                    .iter()
                    .find(|record| record.term_hash == term_hash)
                    .map(|record| record.abstract_instantiation_id.clone());
                if trace_instantiations {
                    trace!(
                        "[yardbird::inst-trace] regular concrete abstract-hash={} abstract-id={abstract_id:?} concrete-term={}",
                        term_hash,
                        inst
                    );
                }
                let added = smt.add_instantiation(inst, abstract_id);
                if trace_instantiations {
                    trace!(
                        "[yardbird::inst-trace] regular add-result abstract-hash={} added={added}",
                        term_hash
                    );
                }
                !added
            })
            .fold(true, |a, b| a && b);

        Ok(())
    }

    fn take_logging_artifacts(
        &mut self,
    ) -> (Vec<DecisionRecord>, Vec<AbstractInstantiationRecord>) {
        (
            mem::take(&mut self.decision_data),
            mem::take(&mut self.abstract_instantiations),
        )
    }

    fn result(
        &mut self,
        vmt_model: &mut VMTModel,
        smt: &dyn crate::solver_interface::SolverInterface,
    ) -> ProofLoopResult {
        for instantiation_term in &smt.get_instantiations() {
            vmt_model.add_instantiation(instantiation_term);
        }
        let found_proof = if self.run_ic3ia {
            match call_ic3ia(vmt_model.clone()) {
                Ok(out) => {
                    info!("IC3IA OUT: {out}");
                    ic3ia_output_contains_proof(out)
                }
                Err(_) => false,
            }
        } else {
            false
        };
        ProofLoopResult {
            model: Some(vmt_model.clone()),
            used_instances: mem::take(&mut smt.get_instantiations()),
            const_instances: mem::take(&mut self.const_instantiations),
            total_instantiations_added: smt.get_number_instantiations_added(),
            total_refinement_steps: 0,
            solver_statistics: smt.get_solver_statistics(),
            counterexample: false,
            found_proof,
            unsat_core: None, // VMT mode unsat core tracked separately via dump-unsat-core
            decision_data: mem::take(&mut self.decision_data),
            abstract_instantiations: mem::take(&mut self.abstract_instantiations),
            indexed_instantiations: vec![],
            unsat_events: vec![],
        }
    }
}
