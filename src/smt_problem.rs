use std::vec;

use log::debug;
use smt2parser::{
    concrete::Term,
    vmt::{bmc::BMCBuilder, quantified_instantiator::Instance, variable::Variable, VMTModel},
};
use z3::ast::Dynamic;

use crate::{
    proof_tree::ProofTree, strategies::ProofStrategy, subterm_handler::SubtermHandler,
    utils::SolverStatistics, z3_var_context::Z3VarContext,
};

pub struct SMTProblem<'ctx> {
    z3_var_context: Z3VarContext<'ctx>,
    bmc_builder: BMCBuilder,
    init_assertion: Term,
    trans_assertion: Term,
    depth: u16,
    instantiations: Vec<Instance>,
    subterm_handler: SubtermHandler,
    pub variables: Vec<Variable>,
    solver: z3::Solver<'ctx>,
    newest_model: Option<z3::Model<'ctx>>,
}

#[allow(clippy::borrowed_box)]
impl<'ctx> SMTProblem<'ctx> {
    pub(crate) fn new<S>(
        vmt_model: &VMTModel,
        context: &'ctx z3::Context,
        strategy: &Box<dyn ProofStrategy<'_, S>>,
    ) -> Self {
        let current_vars = vmt_model.get_all_current_variable_names();
        let next_to_current_vars = vmt_model.get_next_to_current_varible_names();
        let init_assertion = vmt_model.get_initial_condition_for_yardbird();
        let trans_assertion = vmt_model.get_trans_condition_for_yardbird();
        let solver = z3::Solver::new_for_logic(context, strategy.get_logic_string()).unwrap();
        let property_assertion = vmt_model.get_property_for_yardbird();
        let mut smt = SMTProblem {
            subterm_handler: SubtermHandler::new(
                init_assertion.clone(),
                trans_assertion.clone(),
                property_assertion.clone(),
            ),
            init_assertion,
            trans_assertion,
            instantiations: vec![],
            depth: 0,
            bmc_builder: BMCBuilder::new(current_vars, next_to_current_vars),
            variables: vmt_model.get_state_holding_variables(),
            solver,
            z3_var_context: Z3VarContext::new(context),
            newest_model: None,
        };
        if strategy.abstract_array_theory() {
            // Add in abstracted function definitions to Z3VarContext
            for function_def in vmt_model.get_function_definitions() {
                let _ = function_def.accept(&mut smt.z3_var_context);
            }
        }

        // Add initial 0-state variables here, so in the future we only have to add, depth + 1 variables.
        for variable in &smt.variables {
            let bmc_variable = variable
                .current
                .clone()
                .accept(&mut smt.bmc_builder)
                .unwrap();
            let _ = bmc_variable.accept(&mut smt.z3_var_context);
        }
        // Generate initial subterms.
        smt.subterm_handler.generate_subterms(&mut smt.bmc_builder);
        // Add initial assertion.
        smt.add_assertion();
        smt
    }

    /// Adds in all variables at the current depth that is recorded in self.bmc_builder.
    fn add_z3_variables(&mut self) {
        for variable in &self.variables {
            let bmc_variable = variable
                .current
                .clone()
                .accept(&mut self.bmc_builder)
                .unwrap();
            let _ = bmc_variable.accept(&mut self.z3_var_context);
        }
    }

    pub fn get_model(&self) -> &Option<z3::Model> {
        &self.newest_model
    }

    fn add_assertion(&mut self) {
        if self.depth == 0 {
            let init = self
                .bmc_builder
                .index_single_step_term(self.init_assertion.clone());
            let z3_init = self.z3_var_context.rewrite_term(&init);
            self.solver.assert(&z3_init.as_bool().unwrap());
        }
        if self.depth != 0 {
            let trans = self
                .bmc_builder
                .index_transition_term(self.trans_assertion.clone());
            let z3_trans = self.z3_var_context.rewrite_term(&trans);
            self.solver.assert(&z3_trans.as_bool().unwrap());
        }
        if !self.instantiations.is_empty() {
            // Instantiate for this depth.
            let mut all_z3_insts = vec![];
            for inst in &self.instantiations {
                let indexed_inst = inst.rewrite(&mut self.bmc_builder);
                let z3_inst = self.z3_var_context.rewrite_term(&indexed_inst);
                all_z3_insts.push(z3_inst.as_bool().unwrap());
            }
            let inst_and = self.z3_var_context.make_and(all_z3_insts);
            self.solver.assert(&inst_and);
        }
    }

    // All instantiations have been added self.current_depth number of times when
    // this function is called. We only need to unroll transition and all instantiations
    // one more time.
    pub(crate) fn unroll(&mut self, depth: u16) {
        if depth > self.depth {
            // These things should only happen the first time a new depth is seen.
            // Set new depth.
            self.depth = depth;
            self.bmc_builder.set_depth(self.depth);
            // Generate subterms.
            self.subterm_handler
                .generate_subterms(&mut self.bmc_builder);
            // Add new variables to Z3VarContext for depth.
            self.add_z3_variables();
            // Add assertion for current depth.
            self.add_assertion();
        }
    }

    /// Checks the satisfiability of BMC `self.bmc_builder.depth`. Handles pushing and popping the property
    /// off of the solver. Keeping the invariant of the property never being on the solver until check
    /// time allows us to not worry about when to add instances and other facts to the solver.
    ///
    /// NOTE: We have to get the model here and set it because once we pop the solver, that model will
    /// be lost.
    pub(crate) fn check(&mut self) -> z3::SatResult {
        // Push property back on top of the solver.
        self.push_property();
        let sat_result = self.solver.check();
        self.newest_model = self.solver.get_model();
        match self.solver.get_proof() {
            Some(proof) => {
                ProofTree::new(proof);
            }
            None => debug!("NO PROOF!"),
        }
        // Popping property off.
        self.solver.pop(1);
        sat_result
    }

    fn push_property(&mut self) {
        self.solver.push();
        let prop = self.subterm_handler.get_property_assert();
        let z3_prop_negated =
            z3::ast::Bool::not(&self.z3_var_context.rewrite_term(&prop).as_bool().unwrap());
        self.solver.assert(&z3_prop_negated);
    }

    pub(crate) fn add_instantiation(&mut self, inst: Instance) -> bool {
        if self.instantiations.contains(&inst) {
            debug!("ALREADY SEEN {}!", inst);
            return false;
        } else {
            self.instantiations.push(inst.clone());
        }
        // Add in any quantified variables to Z3VarContext.
        if let Term::Forall { vars, term: _ } = inst.get_term() {
            for (symbol, sort) in vars {
                self.z3_var_context.create_variable(symbol, sort);
            }
        }
        debug!("USED INSTANCE: {}", inst);
        // We have to unroll the instantiation for 0-self.bmc_builder
        self.unroll_instantiation(&inst);
        true
    }

    /// We unroll the new instantiation from 0 to the current BMC depth. This allows us
    /// to just worry about the next unrolling in add_assertion().
    fn unroll_instantiation(&mut self, inst: &Instance) {
        let mut all_z3_insts = vec![];
        // The additional unrolling we need depends on the instance itself, if all
        // variables are current, then we need 2 more, if not just 1.
        let cur_depth = self.bmc_builder.depth;
        let number_of_unrollings = if cur_depth == 0 {
            1
        } else {
            cur_depth + inst.additional_depth()
        };
        for i in 0..number_of_unrollings {
            self.bmc_builder.set_depth(i);
            let indexed_inst = inst.rewrite(&mut self.bmc_builder);
            // Have to get the subterms.
            self.subterm_handler
                .register_instantiation_term(indexed_inst.clone());
            let z3_inst = self.z3_var_context.rewrite_term(&indexed_inst);
            all_z3_insts.push(z3_inst.as_bool().unwrap());
        }
        // reset depth
        self.bmc_builder.set_depth(cur_depth);
        let inst_and = self.z3_var_context.make_and(all_z3_insts);
        self.solver.assert(&inst_and);
    }

    pub(crate) fn get_solver_statistics(&self) -> SolverStatistics {
        SolverStatistics::from_z3_statistics(self.solver.get_statistics())
    }

    pub(crate) fn get_reason_unknown(&self) -> Option<String> {
        self.solver.get_reason_unknown()
    }

    pub(crate) fn rewrite_term(&self, term: &Term) -> Dynamic {
        self.z3_var_context.rewrite_term(term)
    }

    pub(crate) fn get_property_subterms(&self) -> Vec<String> {
        self.subterm_handler.get_property_subterms()
    }

    pub(crate) fn get_reads_and_writes(&self) -> smt2parser::vmt::ReadsAndWrites {
        self.subterm_handler.get_reads_and_writes()
    }

    pub(crate) fn get_all_subterms(&self) -> Vec<&Term> {
        self.subterm_handler.get_all_subterms()
    }

    pub(crate) fn to_smtinterpol(&self) -> String {
        todo!()
    }

    pub(crate) fn get_instantiations(&self) -> Vec<Term> {
        self.instantiations
            .iter()
            .map(|inst| inst.get_term().clone())
            .collect()
    }

    pub(crate) fn get_init_and_transition_subterms(&self) -> Vec<String> {
        let mut trans = self.subterm_handler.get_transition_system_subterms();
        trans.extend(self.subterm_handler.get_initial_subterms());
        trans.extend(self.subterm_handler.get_instantiation_subterms());
        trans
    }

    pub(crate) fn get_interpretation(
        &self,
        model: &z3::Model<'ctx>,
        z3_term: &Dynamic<'ctx>,
    ) -> Dynamic<'_> {
        self.z3_var_context.get_interpretation(model, z3_term)
    }
}
