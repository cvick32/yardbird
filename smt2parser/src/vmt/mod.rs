use std::collections::HashMap;

use action::Action;
use array_abstractor::ArrayAbstractor;
use bmc::BMCBuilder;
use itertools::Itertools;
use smt::SMTProblem;
use utils::{get_transition_system_component, get_variables_and_actions};
use variable::Variable;

use crate::concrete::{Command, FunctionDec, Identifier, Sort, Symbol, SyntaxBuilder, Term};

static PROPERTY_ATTRIBUTE: &str = "invar-property";
static TRANSITION_ATTRIBUTE: &str = "trans";
static INITIAL_ATTRIBUTE: &str = "init";

mod action;
mod array_abstractor;
mod bmc;
mod smt;
mod utils;
mod variable;

/// VMTModel represents a transition system given in VMT format.
/// The VMT specification is no longer available but there is an example here:
/// https://es-static.fbk.eu/people/griggio/ic3ia/
#[derive(Clone, Debug)]
pub struct VMTModel {
    sorts: Vec<Command>,
    state_variables: Vec<Variable>,
    function_definitions: Vec<Command>,
    actions: Vec<Action>,
    initial_condition: Term,
    transition_condition: Term,
    property_condition: Term,
}

#[derive(Debug)]
pub enum VMTError {
    UnknownCommand(String),
}

impl VMTModel {
    pub fn checked_from(commands: Vec<Command>) -> Result<Self, VMTError> {
        let number_of_commands = commands.len();
        assert!(number_of_commands > 3, "Not enough commands for VMT model!");
        let property_condition: Term =
            get_transition_system_component(&commands[number_of_commands - 1], PROPERTY_ATTRIBUTE);
        let transition_condition: Term = get_transition_system_component(
            &commands[number_of_commands - 2],
            TRANSITION_ATTRIBUTE,
        );
        let initial_condition: Term =
            get_transition_system_component(&commands[number_of_commands - 3], INITIAL_ATTRIBUTE);
        let mut variable_commands: HashMap<String, Command> = HashMap::new();
        let mut sorts: Vec<Command> = vec![];
        let mut variable_relationships = vec![];
        let mut function_definitions = vec![];
        for (i, command) in commands.iter().enumerate() {
            if i < number_of_commands - 3 {
                // Check whether a variable should be action, state, or local
                match command {
                    Command::DeclareFun {
                        symbol,
                        parameters,
                        sort: _,
                    } => {
                        if parameters.is_empty() {
                            variable_commands.insert(symbol.0.clone(), command.clone());
                        } else {
                            function_definitions.push(command.clone());
                        }
                    }
                    Command::DefineFun { sig: _, term: _ } => {
                        variable_relationships.push(command);
                    }
                    Command::DeclareSort {
                        symbol: _,
                        arity: _,
                    } => {
                        sorts.push(command.clone());
                    }
                    _ => return Err(VMTError::UnknownCommand(command.to_string())),
                }
            }
        }
        let (state_variables, actions) =
            get_variables_and_actions(variable_relationships, variable_commands);

        Ok(VMTModel {
            sorts,
            function_definitions,
            state_variables,
            actions,
            initial_condition,
            transition_condition,
            property_condition,
        })
    }

    /// Clones the current model, rewrites all usages of Arrays into uninterpreted functions
    /// and returns the abstracted VMTModel.
    pub fn abstract_array_theory(&self) -> VMTModel {
        let mut array_types: HashMap<String, String> = HashMap::new();
        array_types.insert("Int".to_string(), "Int".to_string());
        let mut abstractor = ArrayAbstractor {
            visitor: SyntaxBuilder,
            array_types,
        };
        let mut abstracted_commands = vec![];
        for command in self.as_commands() {
            abstracted_commands.push(command.accept(&mut abstractor).unwrap());
        }
        let mut array_definitions = abstractor.get_array_type_definitions();
        array_definitions.extend(abstracted_commands);
        VMTModel::checked_from(array_definitions).unwrap()
    }

    pub fn unroll(&self, length: u8) -> SMTProblem {
        let mut builder = BMCBuilder {
            visitor: SyntaxBuilder,
            current_variables: self.get_all_current_variable_names(),
            next_variables: self.get_all_next_variable_names(),
            step: 0,
        };
        let mut smt_problem = SMTProblem::new(&self.sorts, &self.function_definitions);

        smt_problem.add_assertion(&self.initial_condition, builder.clone());
        for _ in 0..length {
            // Must add variable definitions for each variable at each time step.
            smt_problem.add_variable_definitions(
                &self.state_variables,
                &self.actions,
                builder.clone(),
            );
            smt_problem.add_assertion(&self.transition_condition, builder.clone());
            builder.add_step();
        }
        // Don't forget the variable definitions at time `length`.
        smt_problem.add_variable_definitions(&self.state_variables, &self.actions, builder.clone());
        smt_problem.add_property_assertion(&self.property_condition, builder.clone());
        assert!(
            smt_problem.init_and_trans_length() == (length + 1).into(),
            "Unrolling gives incorrect number of steps {} for length {}.",
            smt_problem.init_and_trans_length(),
            length
        );
        smt_problem
    }

    pub fn as_commands(&self) -> Vec<Command> {
        let mut commands = self.sorts.clone();
        commands.extend(self.function_definitions.clone());
        for variable in self.state_variables.clone() {
            commands.extend(variable.as_commands());
        }
        for action in self.actions.clone() {
            commands.extend(action.as_commands());
        }
        let init_command = Command::DefineFun {
            sig: FunctionDec {
                name: Symbol("init".to_string()),
                parameters: vec![],
                result: Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Bool".to_string()),
                    },
                },
            },
            term: self.initial_condition.clone(),
        };
        commands.push(init_command);
        let trans_command = Command::DefineFun {
            sig: FunctionDec {
                name: Symbol("trans".to_string()),
                parameters: vec![],
                result: Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Bool".to_string()),
                    },
                },
            },
            term: self.transition_condition.clone(),
        };
        commands.push(trans_command);
        let prop_command = Command::DefineFun {
            sig: FunctionDec {
                name: Symbol("prop".to_string()),
                parameters: vec![],
                result: Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Bool".to_string()),
                    },
                },
            },
            term: self.property_condition.clone(),
        };
        commands.push(prop_command);

        commands
    }

    pub fn print_stats(&self) {
        println!("Number of Variables: {}", self.state_variables.len());
        println!("Number of Actions: {}", self.actions.len());
        println!("Number of Sorts: {}", self.sorts.len());
    }

    pub fn as_vmt_string(&self) -> String {
        self.as_commands()
            .iter()
            .map(|command| format!("{}", command.clone().accept(&mut SyntaxBuilder).unwrap()))
            .join("\n")
    }

    fn get_all_current_variable_names(&self) -> Vec<String> {
        let mut state_variable_names: Vec<String> = self
            .state_variables
            .iter()
            .map(|var| var.get_current_variable_name().clone())
            .collect();
        let mut action_names: Vec<String> = self
            .actions
            .iter()
            .map(|action| action.get_current_action_name().clone())
            .collect();
        state_variable_names.append(&mut action_names);
        state_variable_names
    }

    fn get_all_next_variable_names(&self) -> HashMap<String, String> {
        self.state_variables
            .iter()
            .map(|var| {
                (
                    var.get_next_variable_name().clone(),
                    var.get_current_variable_name().clone(),
                )
            })
            .collect()
    }
}
