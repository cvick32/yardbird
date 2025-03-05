use std::vec;

use smt2parser::{
    concrete::Term,
    vmt::{variable::Variable, VMTModel},
};
use z3::ast::Dynamic;

use crate::z3_var_context::Z3VarContext;

use smt2parser::vmt::bmc::BMCBuilder;

pub struct SMTProblem<'ctx> {
    z3_var_context: Z3VarContext<'ctx>,
    bmc_builder: BMCBuilder,
    init_assertion: Term,
    trans_assertion: Term,
    depth: u8,
    instantiations: Vec<Term>,
    subterms: Vec<Term>,
    property_assertion: Term,
    variables: Vec<Variable>,
    solver: z3::Solver<'ctx>,
}
impl<'ctx> SMTProblem<'ctx> {
    pub(crate) fn new(vmt_model: &VMTModel, context: &'ctx z3::Context) -> Self {
        let current_vars = vmt_model.get_all_current_variable_names();
        let next_to_current_vars = vmt_model.get_next_to_current_varible_names();
        let mut smt = SMTProblem {
            init_assertion: vmt_model.get_initial_condition_for_yardbird(),
            trans_assertion: vmt_model.get_trans_condition_for_yardbird(),
            instantiations: vec![],
            subterms: vec![],
            depth: 0,
            property_assertion: vmt_model.get_property_for_yardbird(),
            bmc_builder: BMCBuilder::new(current_vars, next_to_current_vars),
            variables: vmt_model.get_state_holding_variables(),
            solver: z3::Solver::new(context),
            z3_var_context: Z3VarContext::new(context),
        };

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
        self.bmc_builder.set_step(self.depth + 1);
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
        self.bmc_builder.set_step(self.depth);
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
    }

    // All instantiations have been added self.current_depth number of times when
    // this function is called. We only need to unroll transition and all instantiations
    // one more time.
    pub(crate) fn unroll_once(&mut self, depth: u8) {
        // Set new depth.
        self.depth = depth;
        // Add new variables to Z3VarContext for depth.
        self.add_z3_variables();

        // Popping old property off.
        self.solver.pop(1);

        // Add assertion for current depth.
        self.add_assertion();

        // Add instantiations for depth.

        // TODO: Add subterms for new depth as well.

        // Push property back on top of the solver.
        self.push_property();
        self.bmc_builder.set_step(depth);
    }

    pub(crate) fn add_instantiations(&mut self, instantiations: Vec<Term>) {
        //self.solver.pop();
        for inst in instantiations {
            self.unroll_instantiation(&inst);
            self.instantiations.push(inst);
        }
        self.push_property();
    }

    pub(crate) fn check(&mut self) -> z3::SatResult {
        self.solver.check()
    }

    fn push_property(&mut self) {
        self.bmc_builder.set_step(self.depth + 1);
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

    fn unroll_instantiation(&self, inst: &Term) {
        todo!()
    }

    pub(crate) fn get_reason_unknown(&self) -> Option<String> {
        self.solver.get_reason_unknown()
    }

    pub(crate) fn get_assert_terms(&self) -> Vec<Term> {
        todo!()
    }

    pub(crate) fn rewrite_term(&self, simplified_term: &Term) -> Dynamic {
        todo!()
    }

    pub(crate) fn get_transition_system_subterms(&self) -> Vec<String> {
        todo!()
    }

    pub(crate) fn get_property_subterms(&self) -> Vec<String> {
        todo!()
    }

    pub(crate) fn get_reads_and_writes(&self) -> smt2parser::vmt::ReadsAndWrites {
        todo!()
    }

    pub(crate) fn get_all_subterms(&self) -> Vec<Term> {
        todo!()
    }

    pub(crate) fn to_smtinterpol(&self) -> String {
        todo!()
    }
}
