use std::{collections::HashMap, vec};

use serde::de;
use smt2parser::{
    concrete::Term,
    vmt::{self, variable::Variable, VMTModel},
};

use crate::z3_var_context::Z3VarContext;

#[derive(Debug, Clone)]
pub struct SMTProblem {
    //z3_var_context: Z3VarContext,
    init_assertions: Vec<Term>,
    trans_assertions: Vec<Term>,
    instantiations: Vec<Term>,
    subterms: Vec<Term>,
    property_assertion: Term,
    current_depth: u8,
    variables: Vec<Variable>,
}
impl SMTProblem {
    pub(crate) fn new(vmt_model: &VMTModel) -> Self {
        let vars = vmt_model.get_state_variables();
        SMTProblem {
            init_assertions: vec![vmt_model.get_initial_term().clone()],
            trans_assertions: vec![vmt_model.get_trans_term().clone()],
            instantiations: vec![],
            subterms: vec![],
            property_assertion: vmt_model.get_property_term().clone(),
            current_depth: 0,
            variables: vars.to_vec(),
        }
    }

    // All instantiations have been added self.current_depth number of times when
    // this function is called. We only need to unroll transition and all instantiations
    // one more time.
    pub(crate) fn unroll_once(&mut self, depth: u8) {
        // Set new depth.
        self.current_depth = depth;

        // Add new variables to Z3VarContext for depth.

        // Add subterms for new depth as well.

        // Popping old property off.
        // self.solver.pop(1);
        // for transition in self.trans_assertions {
        //     self.solver.add_assertion(transition.unroll(depth));
        // }
        // for instantiation in self.instantiations {
        //     self.solver.add_assertion(instantiation.unroll(depth));
        // }
        // Push property back on top of the solver.

        self.push_property();
    }

    pub(crate) fn add_instantiations(&mut self, instantiations: Vec<Term>) {
        self.solver.pop();
        for inst in instantiations {
            self.unroll_instantiation(inst);
            self.instantiations.push(inst);
        }
        self.push_property();
    }

    pub(crate) fn check(&self) -> z3::SatResult {
        todo!()
    }

    fn push_property(&self) -> _ {
        todo!()
    }

    fn unroll_instantiation(&self, inst: Term) -> _ {
        todo!()
    }
}
