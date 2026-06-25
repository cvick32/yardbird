use log::debug;
use smt2parser::concrete::Term;
use smt2parser::vmt::{bmc::BMCBuilder, quantified_instantiator::Instance};

use crate::{
    solver::YardbirdSolver, subterm_handler::SubtermHandler, training::IndexedInstantiationRecord,
};

use super::{InstantiationStrategy, StoredInstantiation};

/// Default instantiation strategy that fully unrolls all instances from depth 0 to current depth
/// when they are first added.
///
/// This replicates the original behavior from SMTProblem:
/// - Checks for duplicate instances
/// - Registers quantified variables with the solver backend
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
        instantiations: &mut Vec<StoredInstantiation>,
        abstract_instantiation_id: Option<String>,
        _depth: u16,
        bmc_builder: &mut BMCBuilder,
        solver: &mut dyn YardbirdSolver,
        subterm_handler: &mut SubtermHandler,
        track_instantiations: bool,
        tracked_labels: &mut Vec<IndexedInstantiationRecord>,
        asserted_instantiations: &mut Vec<Term>,
        num_quantifiers_instantiated: &mut u64,
    ) {
        // Check for duplicates
        if instantiations.iter().any(|stored| stored.inst == inst) {
            debug!("ALREADY SEEN {}!", inst);
            return;
        }

        debug!("USED INSTANCE: {}", inst);
        instantiations.push(StoredInstantiation {
            inst: inst.clone(),
            abstract_instantiation_id: abstract_instantiation_id.clone(),
        });

        solver
            .register_quantified_variables(inst.get_term())
            .expect("solver should register quantified variables");

        // Unroll the instantiation from 0 to current depth
        // (This is the logic from SMTProblem::unroll_instantiation)
        let mut all_indexed_insts = vec![];
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
            asserted_instantiations.push(indexed_inst.clone());

            all_indexed_insts.push(indexed_inst);
        }

        // Reset depth
        bmc_builder.set_depth(cur_depth);
        *num_quantifiers_instantiated += all_indexed_insts.len() as u64;

        if track_instantiations {
            // Use assert_and_track for each instantiation
            for (idx, indexed_term) in all_indexed_insts.iter().enumerate() {
                let inst_num = tracked_labels.len();
                let label = format!("inst_{}_{}", inst_num, idx);
                solver
                    .assert_tracked_instantiation(label.as_str(), indexed_term)
                    .expect("solver should assert tracked instantiations");
                tracked_labels.push(IndexedInstantiationRecord {
                    label,
                    term: indexed_term.to_string(),
                    term_hash: crate::training::canonical_term_hash_from_string(
                        &indexed_term.to_string(),
                    ),
                    depth: cur_depth,
                    unroll_index: idx as u16,
                    abstract_instantiation_id: abstract_instantiation_id.clone(),
                    in_unsat_core: false,
                });
            }
        } else {
            solver
                .assert_instantiation_batch(&all_indexed_insts)
                .expect("solver should assert instantiations");
        }
    }

    fn on_loop(
        &mut self,
        depth: u16,
        instantiations: &[StoredInstantiation],
        bmc_builder: &mut BMCBuilder,
        solver: &mut dyn YardbirdSolver,
        track_instantiations: bool,
        tracked_labels: &mut Vec<IndexedInstantiationRecord>,
        asserted_instantiations: &mut Vec<Term>,
        num_quantifiers_instantiated: &mut u64,
    ) {
        // At each new depth, we need to add all existing instantiations for that depth
        // This completes the "full unroll" behavior
        if instantiations.is_empty() {
            return;
        }

        let mut all_indexed_insts = vec![];
        for stored in instantiations {
            bmc_builder.set_width(stored.inst.width());
            let indexed_inst = stored.inst.rewrite(bmc_builder);
            asserted_instantiations.push(indexed_inst.clone());
            all_indexed_insts.push((indexed_inst, stored.abstract_instantiation_id.clone()));
        }

        *num_quantifiers_instantiated += all_indexed_insts.len() as u64;

        if track_instantiations {
            // Use assert_and_track for each instantiation
            for (indexed_term, abstract_instantiation_id) in all_indexed_insts {
                let inst_num = tracked_labels.len();
                let label = format!("inst_{}_depth_{}", inst_num, depth);
                solver
                    .assert_tracked_instantiation(label.as_str(), &indexed_term)
                    .expect("solver should assert tracked instantiations");
                let term_string = indexed_term.to_string();
                tracked_labels.push(IndexedInstantiationRecord {
                    label,
                    term_hash: crate::training::canonical_term_hash_from_string(&term_string),
                    term: term_string,
                    depth,
                    unroll_index: 0,
                    abstract_instantiation_id,
                    in_unsat_core: false,
                });
            }
        } else {
            let terms = all_indexed_insts
                .into_iter()
                .map(|(indexed_term, _)| indexed_term)
                .collect::<Vec<_>>();
            solver
                .assert_instantiation_batch(&terms)
                .expect("solver should assert instantiations");
        }
    }
}
