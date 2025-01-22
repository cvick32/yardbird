use std::mem;

use anyhow::anyhow;
use log::{debug, info};
use smt2parser::{
    concrete::Term,
    get_term_from_term_string,
    vmt::{smt::SMTProblem, VMTModel},
};
use z3::Model;

use crate::{
    analysis::SaturationInequalities, array_axioms::ArrayLanguage,
    cost_functions::symbol_cost::BestSymbolSubstitution, egg_utils::Saturate,
    z3_var_context::Z3VarContext, ProofLoopResult,
};

use super::{ProofAction, ProofStrategy};

/// Global state carried across different BMC depths
#[derive(Default)]
pub struct Abstract {
    used_instantiations: Vec<String>,
    const_instantiations: Vec<String>,
    bmc_depth: u8,
}

impl Abstract {
    pub fn new(bmc_depth: u8) -> Self {
        Self {
            bmc_depth,
            ..Default::default()
        }
    }

    fn _check_found_instantiations(
        &self,
        z3_var_context: &Z3VarContext,
        model: &Model,
        insts: Vec<String>,
    ) -> (Vec<String>, Vec<(Term, Term)>) {
        let mut true_insts = vec![];
        let mut false_insts = vec![];
        for inst in &insts {
            let term = get_term_from_term_string(inst);
            let z3_term = z3_var_context.rewrite_term(&term);

            println!("{term}");
            let (lhs, rhs) = match term {
                smt2parser::concrete::Term::Application {
                    qual_identifier,
                    arguments,
                } => {
                    if qual_identifier.get_name().eq("=") {
                        (arguments[0].clone(), arguments[1].clone())
                    } else if qual_identifier.get_name().eq("=>") {
                        match &arguments[1] {
                            Term::Application {
                                qual_identifier: _,
                                arguments,
                            } => (arguments[0].clone(), arguments[1].clone()),
                            _ => panic!(),
                        }
                    } else {
                        panic!("must be equality or implies");
                    }
                }
                _ => panic!("Must be equality!"),
            };
            // TODO: we need to interrupt here if we find any true instantiations, add them to the
            // egraph, and saturate again.... that's pretty annoying.
            match model.eval(&z3_term, false) {
                Some(truth) => {
                    if !truth.as_bool().unwrap().as_bool().unwrap() {
                        false_insts.push(inst.clone());
                    } else {
                        true_insts.push((lhs, rhs));
                    }
                }
                None => todo!(),
            }
        }
        (false_insts, true_insts)
    }
}

/// State for the inner refinement looop
pub struct AbstractRefinementState {
    pub smt: SMTProblem,
    pub depth: u8,
    pub egraph: egg::EGraph<ArrayLanguage, SaturationInequalities>,
    pub instantiations: Vec<String>,
    pub const_instantiations: Vec<String>,
}

impl ProofStrategy<'_, AbstractRefinementState> for Abstract {
    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        model
            .abstract_array_theory()
            .abstract_constants_over(self.bmc_depth)
    }

    fn setup(&mut self, smt: SMTProblem, depth: u8) -> anyhow::Result<AbstractRefinementState> {
        let mut egraph = egg::EGraph::new(SaturationInequalities).with_explanations_enabled();
        for term in smt.get_assert_terms() {
            // TODO: we don't want to add instantiations
            if let Ok(parsed) = &term.to_string().parse() {
                egraph.add_expr(parsed);
            }
        }
        Ok(AbstractRefinementState {
            smt,
            depth,
            egraph,
            instantiations: vec![],
            const_instantiations: vec![],
        })
    }

    fn unsat(
        &mut self,
        state: &mut AbstractRefinementState,
        _solver: &z3::Solver,
    ) -> anyhow::Result<ProofAction> {
        info!("RULED OUT ALL COUNTEREXAMPLES OF DEPTH {}", state.depth);
        Ok(ProofAction::NextDepth)
    }

    fn sat(
        &mut self,
        state: &mut AbstractRefinementState,
        solver: &z3::Solver,
        z3_var_context: &Z3VarContext,
    ) -> anyhow::Result<ProofAction> {
        let model = solver.get_model().ok_or(anyhow!("No z3 model"))?;
        debug!("counter example:\n{model}");
        state.update_with_subterms(&model, z3_var_context)?;
        state.egraph.rebuild();
        let cost_fn = BestSymbolSubstitution {
            current_bmc_depth: state.depth as u32,
            transition_system_terms: state.smt.get_transition_system_subterms(),
            property_terms: state.smt.get_property_subterms(),
            reads_writes: state.smt.get_reads_and_writes(),
        };
        let (insts, const_insts) = state.egraph.saturate(cost_fn);
        state.instantiations.extend_from_slice(&insts);
        state.const_instantiations.extend_from_slice(&const_insts);
        Ok(ProofAction::Continue)
    }

    fn finish(
        &mut self,
        model: &mut VMTModel,
        state: AbstractRefinementState,
    ) -> anyhow::Result<()> {
        self.const_instantiations
            .extend_from_slice(&state.const_instantiations);

        let no_progress = state
            .instantiations
            .into_iter()
            .all(|inst| !model.add_instantiation(inst, &mut self.used_instantiations));
        let const_progress = state
            .const_instantiations
            .into_iter()
            .all(|inst| !model.add_instantiation(inst, &mut self.used_instantiations));
        if no_progress && const_progress {
            Err(anyhow!("Failed to add new instantations."))
        } else {
            Ok(())
        }
    }

    fn result(&mut self, vmt_model: VMTModel) -> ProofLoopResult {
        ProofLoopResult {
            model: Some(vmt_model),
            used_instances: mem::take(&mut self.used_instantiations),
            const_instances: mem::take(&mut self.const_instantiations),
            counterexample: false,
            result_type: crate::driver::ProofLoopResultType::Success,
        }
    }

    fn no_progress_result(&mut self, vmt_model: VMTModel) -> ProofLoopResult {
        ProofLoopResult {
            model: Some(vmt_model),
            used_instances: mem::take(&mut self.used_instantiations),
            const_instances: mem::take(&mut self.const_instantiations),
            counterexample: false,
            result_type: crate::driver::ProofLoopResultType::NoProgress,
        }
    }
}

impl AbstractRefinementState {
    pub fn update_with_subterms(
        &mut self,
        model: &z3::Model,
        z3_var_context: &Z3VarContext,
    ) -> anyhow::Result<()> {
        for term in self.smt.get_all_subterms() {
            let term_id = self.egraph.add_expr(&term.to_string().parse()?);
            let z3_term = z3_var_context.rewrite_term(&term);
            let model_interp = model
                .eval(&z3_term, false)
                .unwrap_or_else(|| panic!("Term not found in model: {term}"));
            let interp_id = self.egraph.add_expr(&model_interp.to_string().parse()?);
            self.egraph.union(term_id, interp_id);
            self.egraph.rebuild();
        }
        Ok(())
    }

    fn _add_true_instantiation(
        &mut self,
        lhs: smt2parser::concrete::Term,
        rhs: smt2parser::concrete::Term,
    ) -> anyhow::Result<()> {
        let lhs_id = self.egraph.add_expr(&lhs.to_string().parse()?);
        let rhs_id = self.egraph.add_expr(&rhs.to_string().parse()?);
        debug!("Adding: {} = {}", lhs, rhs);
        self.egraph.union(lhs_id, rhs_id);
        self.egraph.rebuild();
        Ok(())
    }
}

/* let mut full_false_insts = vec![];
let mut full_const_insts = vec![];
let mut i = 0;
loop {
    if i > 15 {
        break;
    }
    state.egraph.rebuild();
    let cost_fn = BestVariableSubstitution {
        current_bmc_depth: state.depth as u32,
        transition_system_terms: state.smt.get_transition_system_subterms(),
        property_terms: state.smt.get_property_subterms(),
    };

    let (insts, const_insts) = state.egraph.saturate(cost_fn);
    let (false_insts, true_insts) =
        self._check_found_instantiations(z3_var_context, &model, insts);
    if false_insts.is_empty() {
        for (lhs, rhs) in true_insts {
            println!("Add: {} = {}", lhs, rhs);
            state._add_true_instantiation(lhs, rhs)?;
        }
    } else {
        full_false_insts.extend_from_slice(&false_insts);
        full_const_insts.extend_from_slice(&const_insts);
        break;
    }
    i += 1;
}
println!("ACTUALLY FALSE INSTS: {:#?}", full_false_insts); */
