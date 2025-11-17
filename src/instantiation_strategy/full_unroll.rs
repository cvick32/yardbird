use log::debug;
use smt2parser::{
    concrete::Term,
    vmt::{bmc::BMCBuilder, quantified_instantiator::Instance},
};

use crate::{subterm_handler::SubtermHandler, z3_var_context::Z3VarContext};

use super::InstantiationStrategy;

/// Default instantiation strategy that fully unrolls all instances from depth 0 to current depth
/// when they are first added.
///
/// This replicates the original behavior from SMTProblem:
/// - Checks for duplicate instances
/// - Registers quantified variables with Z3
/// - Unrolls the instance from 0 to current depth when added
/// - Does nothing during on_loop (all unrolling happens in on_generate)
#[derive(Clone, Debug)]
pub struct FullUnrollStrategy;

impl FullUnrollStrategy {
    pub fn new() -> Self {
        FullUnrollStrategy
    }
}

impl Default for FullUnrollStrategy {
    fn default() -> Self {
        Self::new()
    }
}

impl InstantiationStrategy for FullUnrollStrategy {
    fn clone_box(&self) -> Box<dyn InstantiationStrategy> {
        Box::new(self.clone())
    }

    fn on_generate(
        &mut self,
        inst: Instance,
        instantiations: &mut Vec<Instance>,
        _depth: u16,
        bmc_builder: &mut BMCBuilder,
        z3_var_context: &mut Z3VarContext,
        solver: &mut z3::Solver,
        subterm_handler: &mut SubtermHandler,
        track_instantiations: bool,
        tracked_labels: &mut Vec<(String, Term)>,
        num_quantifiers_instantiated: &mut u64,
    ) {
        // Check for duplicates
        if instantiations.contains(&inst) {
            debug!("ALREADY SEEN {}!", inst);
            return;
        }

        debug!("USED INSTANCE: {}", inst);
        instantiations.push(inst.clone());

        // Add quantified variables to Z3VarContext
        if let Term::Forall { vars, term: _ } = inst.get_term() {
            for (symbol, sort) in vars {
                z3_var_context.create_variable(symbol, sort);
            }
        }

        // Unroll the instantiation from 0 to current depth
        // (This is the logic from SMTProblem::unroll_instantiation)
        let mut all_z3_insts = vec![];
        let cur_depth = bmc_builder.depth;

        for i in (0..=cur_depth).rev() {
            if i < inst.width() {
                break;
            }
            bmc_builder.set_depth(i);
            bmc_builder.set_width(inst.width());
            let indexed_inst = inst.rewrite(bmc_builder);

            // Register subterms from this instantiation
            subterm_handler.register_instantiation_term(indexed_inst.clone());

            let z3_inst = z3_var_context.rewrite_term(&indexed_inst);
            all_z3_insts.push((z3_inst.as_bool().unwrap(), indexed_inst));
        }

        // Reset depth
        bmc_builder.set_depth(cur_depth);
        *num_quantifiers_instantiated += all_z3_insts.len() as u64;

        if track_instantiations {
            // Use assert_and_track for each instantiation
            for (idx, (z3_inst, indexed_term)) in all_z3_insts.iter().enumerate() {
                let inst_num = tracked_labels.len();
                let label = format!("inst_{}_{}", inst_num, idx);
                let tracked_bool = z3::ast::Bool::new_const(label.as_str());
                solver.assert_and_track(z3_inst, &tracked_bool);
                tracked_labels.push((label, indexed_term.clone()));
            }
        } else {
            // Combine all into one assertion
            let inst_and = z3_var_context.make_and(
                all_z3_insts
                    .into_iter()
                    .map(|(z3_inst, _)| z3_inst)
                    .collect(),
            );
            solver.assert(&inst_and);
        }
    }

    fn on_loop(
        &mut self,
        depth: u16,
        instantiations: &[Instance],
        bmc_builder: &mut BMCBuilder,
        z3_var_context: &mut Z3VarContext,
        solver: &mut z3::Solver,
        track_instantiations: bool,
        tracked_labels: &mut Vec<(String, Term)>,
        num_quantifiers_instantiated: &mut u64,
    ) {
        // At each new depth, we need to add all existing instantiations for that depth
        // This completes the "full unroll" behavior
        if instantiations.is_empty() {
            return;
        }

        let mut all_z3_insts = vec![];
        for inst in instantiations {
            bmc_builder.set_width(inst.width());
            let indexed_inst = inst.rewrite(bmc_builder);
            let z3_inst = z3_var_context.rewrite_term(&indexed_inst);
            all_z3_insts.push((z3_inst.as_bool().unwrap(), indexed_inst));
        }

        *num_quantifiers_instantiated += all_z3_insts.len() as u64;

        if track_instantiations {
            // Use assert_and_track for each instantiation
            for (z3_inst, indexed_term) in all_z3_insts {
                let inst_num = tracked_labels.len();
                let label = format!("inst_{}_depth_{}", inst_num, depth);
                let tracked_bool = z3::ast::Bool::new_const(label.as_str());
                solver.assert_and_track(&z3_inst, &tracked_bool);
                tracked_labels.push((label, indexed_term));
            }
        } else {
            // Combine all into one assertion for this depth
            let inst_and = z3_var_context.make_and(
                all_z3_insts
                    .into_iter()
                    .map(|(z3_inst, _)| z3_inst)
                    .collect(),
            );
            solver.assert(&inst_and);
        }
    }
}
