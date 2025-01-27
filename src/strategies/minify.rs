use std::mem;

use anyhow::anyhow;
use smt2parser::{concrete::Term, vmt::VMTModel};

use super::{AbstractRefinementState, ProofStrategy};
use crate::{driver::Result, strategies::ProofAction, Driver, ProofLoopResult};

#[derive(Default)]
pub struct Minify {
    bmc_depth: u8,
    instantiations: Vec<Term>,
}

impl Minify {
    pub fn new(bmc_depth: u8, instantiations: Vec<Term>) -> Self {
        Self {
            bmc_depth,
            instantiations,
        }
    }

    pub fn minify(model: VMTModel, instantiations: Vec<Term>, bmc_depth: u8) -> Vec<Term> {
        let mut unnecessary_term_indices: Vec<usize> = vec![];
        for i in 0..instantiations.len() {
            log::debug!(
                "removing {}/{}: {i} {:?}",
                i + 1,
                instantiations.len(),
                unnecessary_term_indices
            );
            let cfg = z3::Config::new();
            let context = z3::Context::new(&cfg);
            let mut driver = Driver::new(&context, model.clone());

            // filter out i + unnecessary terms
            let test_set = instantiations
                .iter()
                .enumerate()
                .filter_map(|(idx, inst)| {
                    if idx == i || unnecessary_term_indices.contains(&idx) {
                        None
                    } else {
                        Some(inst.clone())
                    }
                })
                .collect();

            let strat = Box::new(Minify::new(bmc_depth, test_set));
            let new_res = driver.check_strategy(bmc_depth, strat);

            if new_res.is_ok() {
                log::debug!("  unnecessary!");
                unnecessary_term_indices.push(i);
            } else {
                log::debug!("  necessary!");
            }
        }

        instantiations
            .into_iter()
            .enumerate()
            .filter_map(|(idx, inst)| {
                if unnecessary_term_indices.contains(&idx) {
                    None
                } else {
                    Some(inst)
                }
            })
            .collect()
    }
}

impl ProofStrategy<'_, AbstractRefinementState> for Minify {
    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        let mut model = model
            .abstract_array_theory()
            .abstract_constants_over(self.bmc_depth);

        // add all passed instantiations into the model
        let mut used = vec![];
        for term in mem::take(&mut self.instantiations) {
            model.add_instantiation(term, &mut used);
        }

        model
    }

    fn n_refines(&mut self) -> u32 {
        1
    }

    fn setup(
        &mut self,
        smt: smt2parser::vmt::smt::SMTProblem,
        depth: u8,
    ) -> Result<AbstractRefinementState> {
        Ok(AbstractRefinementState::new(smt, depth))
    }

    fn unsat(
        &mut self,
        state: &mut AbstractRefinementState,
        _solver: &z3::Solver,
    ) -> Result<super::ProofAction> {
        log::info!("RULED OUT ALL COUNTEREXAMPLES OF DEPTH {}", state.depth);
        Ok(ProofAction::NextDepth)
    }

    fn sat(
        &mut self,
        state: &mut AbstractRefinementState,
        solver: &z3::Solver,
        _z3_var_context: &crate::z3_var_context::Z3VarContext,
    ) -> Result<super::ProofAction> {
        log::info!("Concrete Counterexample Found at depth {}!", state.depth);
        let model = solver.get_model().ok_or(anyhow!("No z3 model"))?;
        log::info!("Counterexample:\n{}", model);
        Ok(ProofAction::Stop)
    }

    fn result(&mut self, model: smt2parser::vmt::VMTModel) -> ProofLoopResult {
        ProofLoopResult {
            model: Some(model),
            used_instances: vec![],
            const_instances: vec![],
            counterexample: false,
        }
    }
}
