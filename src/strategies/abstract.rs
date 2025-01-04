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
    analysis::SaturationInequalities, array_axioms::ArrayLanguage, cost::BestVariableSubstitution,
    egg_utils::Saturate, z3_ext::ModelExt, z3_var_context::Z3VarContext, ProofLoopResult,
};

use super::{ProofAction, ProofStrategy};

/// Global state carried across different BMC depths
#[derive(Default)]
pub struct Abstract {
    used_instantiations: Vec<String>,
    const_instantiations: Vec<String>,
}
impl Abstract {
    fn check_found_instantiations(
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
                                qual_identifier,
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

impl<'ctx> ProofStrategy<'ctx, AbstractRefinementState> for Abstract {
    fn configure_model(&mut self, model: VMTModel) -> VMTModel {
        model.abstract_array_theory()
    }

    fn setup(&mut self, smt: SMTProblem, depth: u8) -> anyhow::Result<AbstractRefinementState> {
        let mut egraph = egg::EGraph::new(SaturationInequalities).with_explanations_enabled();
        for term in smt.get_assert_terms() {
            egraph.add_expr(&term.parse()?);
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
        println!("model:\n{}", model.dump_sorted()?);
        state.update_from_model(&model)?;
        state.update_with_non_array_function_terms(&model, z3_var_context)?;
        state.egraph.rebuild();
        let cost_fn = BestVariableSubstitution {
            current_frame_number: state.depth as u32,
            property_terms: state.smt.get_property_terms(),
        };
        let (insts, const_insts) = state.egraph.saturate(cost_fn);

        /*
        let mut full_false_insts = vec![];
        let mut full_const_insts = vec![];
        let mut i = 0;
        loop {
            if i > 15 {
                break;
            }
            state.egraph.rebuild();
            let cost_fn = BestVariableSubstitution {
                current_frame_number: state.depth as u32,
                property_terms: state.smt.get_property_terms(),
            };
            let (insts, const_insts) = state.egraph.saturate(cost_fn);
            let (false_insts, true_insts) =
                self.check_found_instantiations(z3_var_context, &model, insts);
            if false_insts.is_empty() {
                for (lhs, rhs) in true_insts {
                    println!("Add: {} = {}", lhs, rhs);
                    state.add_true_instantiation(lhs, rhs)?;
                }
            } else {
                full_false_insts.extend_from_slice(&false_insts);
                full_const_insts.extend_from_slice(&const_insts);
                break;
            }
            i += 1;
        }
        println!("ACTUALLY FALSE INSTS: {:#?}", full_false_insts);
        */
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
            Err(anyhow!("Failed to add new instantations"))
        } else {
            Ok(())
        }
    }

    fn result(&mut self) -> ProofLoopResult {
        ProofLoopResult {
            model: None,
            used_instances: mem::take(&mut self.used_instantiations),
            const_instances: mem::take(&mut self.const_instantiations),
            counterexample: false,
        }
    }
}

impl AbstractRefinementState {
    fn update_from_model(&mut self, model: &z3::Model<'_>) -> anyhow::Result<()> {
        for func_decl in model.sorted_iter() {
            if func_decl.arity() == 0 {
                // VARIABLE
                // Apply no arguments to the constant so we can call get_const_interp.
                let func_decl_ast = func_decl.apply(&[]);
                let var = func_decl.name().parse()?;
                let var_id = self.egraph.add_expr(&var);
                let value = model.get_const_interp(&func_decl_ast).ok_or(anyhow!(
                    "Could not find interpretation for variable: {func_decl}"
                ))?;
                let expr = value.to_string().parse()?;
                let value_id = self.egraph.add_expr(&expr);
                self.egraph.union(var_id, value_id);
            } else {
                // FUNCTION DEF
                let interpretation = model
                    .get_func_interp(&func_decl)
                    .ok_or(anyhow!("No function interpretation for: {func_decl}"))?;
                for entry in interpretation.get_entries() {
                    let function_call = format!(
                        "({} {})",
                        func_decl.name(),
                        entry
                            .get_args()
                            .iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(" ")
                    );
                    let funcall = function_call.parse()?;
                    let expr = entry.get_value().to_string().parse()?;
                    let function_id = self.egraph.add_expr(&funcall);
                    let value_id = self.egraph.add_expr(&expr);
                    self.egraph.union(function_id, value_id);
                }
            }
            self.egraph.rebuild();
        }
        Ok(())
    }

    pub fn update_with_non_array_function_terms(
        &mut self,
        model: &z3::Model,
        z3_var_context: &Z3VarContext,
    ) -> anyhow::Result<()> {
        for term in self.smt.get_eq_terms() {
            let term_id = self.egraph.add_expr(&term.to_string().parse()?);
            let z3_term = z3_var_context.rewrite_term(&term);
            let model_interp = model
                .eval(&z3_term, false)
                .unwrap_or_else(|| panic!("Term not found in model: {term}"));
            let interp_id = self.egraph.add_expr(&model_interp.to_string().parse()?);
            println!("Adding: {} = {}", term, model_interp);
            self.egraph.union(term_id, interp_id);
            self.egraph.rebuild();
        }
        Ok(())
    }

    fn add_true_instantiation(
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
