use smt2parser::concrete::{Command, Term};
use smt2parser::vmt::VMTModel;
use std::collections::HashMap;

use crate::problem::{Problem, UnrollableProblem};

/// Implementation of Problem trait for VMTModel (transition systems in VMT format)
impl Problem for VMTModel {
    fn get_sorts(&self) -> Vec<Command> {
        // VMTModel doesn't expose sorts directly, but we can get them from as_commands()
        self.as_commands()
            .into_iter()
            .filter(|cmd| matches!(cmd, Command::DeclareSort { .. }))
            .collect()
    }

    fn get_function_definitions(&self) -> Vec<Command> {
        self.get_function_definitions()
    }

    fn get_logic(&self) -> Option<String> {
        // VMT doesn't specify logic explicitly, it's inferred from the theory
        // This will be determined by the strategy/theory support
        None
    }

    fn requires_unrolling(&self) -> bool {
        // VMT problems are transition systems that require temporal unrolling
        true
    }

    fn as_commands(&self) -> Vec<Command> {
        self.as_commands()
    }
}

/// Implementation of UnrollableProblem for VMTModel
impl UnrollableProblem for VMTModel {
    fn get_initial_condition(&self) -> Term {
        self.get_initial_condition_for_yardbird()
    }

    fn get_transition_condition(&self) -> Term {
        self.get_trans_condition_for_yardbird()
    }

    fn get_property_condition(&self) -> Term {
        self.get_property_for_yardbird()
    }

    fn get_all_current_variable_names(&self) -> Vec<String> {
        self.get_all_current_variable_names()
    }

    fn get_next_to_current_variable_names(&self) -> HashMap<String, String> {
        self.get_next_to_current_varible_names()
    }

    fn add_instantiation(&mut self, term: &Term) -> bool {
        self.add_instantiation(term)
    }
}
