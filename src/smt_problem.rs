use std::vec;

use log::debug;
use smt2parser::{
    concrete::Term,
    vmt::{bmc::BMCBuilder, variable::Variable, VMTModel},
};
use z3::ast::Dynamic;

use crate::{
    strategies::ProofStrategy, subterm_handler::SubtermHandler, z3_var_context::Z3VarContext,
};

pub struct SMTProblem<'ctx> {
    z3_var_context: Z3VarContext<'ctx>,
    bmc_builder: BMCBuilder,
    init_assertion: Term,
    trans_assertion: Term,
    property_assertion: Term,
    depth: u8,
    instantiations: Vec<Term>,
    subterm_handler: SubtermHandler,
    variables: Vec<Variable>,
    solver: z3::Solver<'ctx>,
}
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
        let property_assertion = vmt_model.get_property_for_yardbird();
        let mut smt = SMTProblem {
            subterm_handler: SubtermHandler::new(
                init_assertion.clone(),
                trans_assertion.clone(),
                property_assertion.clone(),
            ),
            init_assertion,
            trans_assertion,
            property_assertion,
            instantiations: vec![],
            depth: 0,
            bmc_builder: BMCBuilder::new(current_vars, next_to_current_vars),
            variables: vmt_model.get_state_holding_variables(),
            solver: z3::Solver::new(context),
            z3_var_context: Z3VarContext::new(context),
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

    pub fn get_model(&self) -> Option<z3::Model> {
        self.solver.get_model()
    }

    fn add_assertion(&mut self) {
        self.bmc_builder.set_depth(self.depth);
        if self.depth == 0 {
            let init = self
                .init_assertion
                .clone()
                .accept(&mut self.bmc_builder)
                .unwrap();
            let z3_init = self.z3_var_context.rewrite_term(&init);
            self.solver.assert(&z3_init.as_bool().unwrap());
        }
        let trans = self
            .trans_assertion
            .clone()
            .accept(&mut self.bmc_builder)
            .unwrap();
        let z3_trans = self.z3_var_context.rewrite_term(&trans);
        self.solver.assert(&z3_trans.as_bool().unwrap());

        if !self.instantiations.is_empty() {
            // Get the instantiations for the next depth.
            let mut all_z3_insts = vec![];
            for inst in &self.instantiations {
                let indexed_inst = inst.clone().accept(&mut self.bmc_builder).unwrap();
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
    pub(crate) fn unroll(&mut self, depth: u8) {
        if depth > self.depth || self.depth == 0 {
            // These things should only happen the first time a new depth is seen.
            // Set new depth.
            self.depth = depth;
            // Temporaily increase depth to generate new depth + 1 variables.
            self.bmc_builder.set_depth(self.depth + 1);
            // Add new variables to Z3VarContext for depth.
            self.add_z3_variables();
            self.bmc_builder.set_depth(self.depth);
            // Generate subterms.
            self.subterm_handler
                .generate_subterms(&mut self.bmc_builder);
            // Add assertion for current depth.
            self.add_assertion();
            self.bmc_builder.set_depth(depth);
        }
    }

    /// Checks the satisfiability of BMC `self.bmc_builder.depth`. Handles pushing and popping the property
    /// off of the solver. Keeping the invariant of the property never being on the solver until check
    /// time allows us to not worry about when to add instances and other facts to the solver.
    pub(crate) fn check(&mut self) -> z3::SatResult {
        // Push property back on top of the solver.
        self.push_property();
        println!("{}", self.solver);
        let sat_result = self.solver.check();
        // Popping property off.
        self.solver.pop(1);
        sat_result
    }

    fn push_property(&mut self) {
        self.bmc_builder.set_depth(self.depth + 1);
        self.solver.push();
        let prop = self
            .property_assertion
            .clone()
            .accept(&mut self.bmc_builder)
            .unwrap();
        let z3_prop_negated =
            z3::ast::Bool::not(&self.z3_var_context.rewrite_term(&prop).as_bool().unwrap());
        self.solver.assert(&z3_prop_negated);
    }

    pub(crate) fn add_instantiation(&mut self, inst: Term) -> bool {
        if self.instantiations.contains(&inst) {
            debug!("ALREADY SEEN {} in {:?}", inst, self.instantiations);
            return false;
        } else {
            self.instantiations.push(inst.clone());
        }
        debug!("USED INSTANCE: {}", inst);
        // We have to unroll the instantiation for 0-self.bmc_builder
        self.unroll_instantiation(&inst);
        true
    }

    /// We unroll the new instantiation from 0 to the current BMC depth. This allows us
    /// to just worry about the next unrolling in add_assertion().
    fn unroll_instantiation(&mut self, inst: &Term) {
        let mut all_z3_insts = vec![];
        // depth + 1 so we grab the depth inst.
        for i in 0..self.bmc_builder.depth + 1 {
            self.bmc_builder.set_depth(i);
            let indexed_inst = inst.clone().accept(&mut self.bmc_builder).unwrap();
            let z3_inst = self.z3_var_context.rewrite_term(&indexed_inst);
            all_z3_insts.push(z3_inst.as_bool().unwrap());
        }
        let inst_and = self.z3_var_context.make_and(all_z3_insts);
        println!("{}: {}", inst, inst_and);
        self.solver.assert(&inst_and);
    }

    pub(crate) fn get_reason_unknown(&self) -> Option<String> {
        self.solver.get_reason_unknown()
    }

    pub(crate) fn get_assert_strings(&self) -> Vec<String> {
        self.subterm_handler.get_assert_strings()
    }

    pub(crate) fn rewrite_term(&self, term: &Term) -> Dynamic {
        self.z3_var_context.rewrite_term(term)
    }

    pub(crate) fn get_transition_system_subterms(&self) -> Vec<String> {
        self.subterm_handler.get_transition_system_subterms()
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
}
