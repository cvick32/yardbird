use std::{collections::HashMap, fs::File, io::Write, path::Path};

use action::Action;
use array_abstractor::ArrayAbstractor;
use axiom::Axiom;
use bmc::BMCBuilder;
use itertools::Itertools;
use log::{debug, info};
use smt::SMTProblem;
use utils::{get_and_terms, get_transition_system_component, get_variables_actions_and_axioms};
use variable::Variable;

use crate::{
    concrete::{self, Command, FunctionDec, Identifier, Sort, Symbol, SyntaxBuilder, Term},
    constant_abstraction::ConstantAbstractor,
    let_extract::LetExtract,
    CommandStream,
};

pub use quantified_instantiator::{Instance, QuantifiedInstantiator, UnquantifiedInstantiator};
pub use reads_and_write::ReadsAndWrites;

static PROPERTY_ATTRIBUTE: &str = "invar-property";
static TRANSITION_ATTRIBUTE: &str = "trans";
static INITIAL_ATTRIBUTE: &str = "init";

mod action;
mod array_abstractor;
mod array_axiom_frame_num_getter;
mod axiom;
pub mod bmc;
pub mod canonicalize_boolean;
pub mod non_boolean_subterms;
pub mod numbered_to_symbolic;
pub mod quantified_instantiator;
mod reads_and_write;
mod smt;
mod smtinterpol_utils;
mod utils;
pub mod variable;

pub static VARIABLE_FRAME_DELIMITER: &str = "@";
pub static NEXT_VARIABLE_NAME: &str = "next";

/// VMTModel represents a transition system given in VMT format.
/// The VMT specification is no longer available but there is an example here:
/// https://es-static.fbk.eu/people/griggio/ic3ia/
#[derive(Clone, Debug)]
pub struct VMTModel {
    sorts: Vec<Command>,
    state_variables: Vec<Variable>,
    function_definitions: Vec<Command>,
    actions: Vec<Action>,
    _axioms: Vec<Axiom>,
    initial_condition: Term,
    transition_condition: Term,
    property_condition: Term,
}

#[derive(Debug)]
pub enum VMTError {
    UnknownCommand(String),
    FileError,
    VisitorError,
}

impl From<std::io::Error> for VMTError {
    fn from(_value: std::io::Error) -> Self {
        VMTError::FileError
    }
}

impl From<concrete::Error> for VMTError {
    fn from(_value: concrete::Error) -> Self {
        VMTError::VisitorError
    }
}

impl VMTModel {
    pub fn from_path(path: impl AsRef<Path>) -> Result<Self, VMTError> {
        let file = std::fs::File::open(path.as_ref())?;
        let reader = std::io::BufReader::new(file);
        let command_stream = CommandStream::new(
            reader,
            SyntaxBuilder,
            Some(path.as_ref().to_string_lossy().to_string()),
        );
        VMTModel::checked_from(
            command_stream
                .into_iter()
                .collect::<Result<Vec<_>, concrete::Error>>()?,
        )
    }

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
        let (state_variables, actions, axioms) =
            get_variables_actions_and_axioms(variable_relationships, variable_commands);

        Ok(VMTModel {
            sorts,
            function_definitions,
            state_variables,
            actions,
            _axioms: axioms,
            initial_condition,
            transition_condition,
            property_condition,
        })
    }

    /// Clones the current model, rewrites all usages of Arrays into uninterpreted functions
    /// and returns the abstracted VMTModel.
    /// TODO: only works for Array Int Int, need to extend to other theories.
    pub fn abstract_array_theory(&self) -> VMTModel {
        let mut array_types: HashMap<String, String> = HashMap::new();
        array_types.insert("Int".to_string(), "Int".to_string());
        let mut abstractor = ArrayAbstractor::default();
        let mut abstracted_commands = vec![];
        for command in self.as_commands() {
            abstracted_commands.push(command.accept(&mut abstractor).unwrap());
        }
        let mut array_definitions = abstractor.get_array_type_definitions();
        array_definitions.extend(abstracted_commands);
        VMTModel::checked_from(array_definitions).unwrap()
    }

    pub fn abstract_constants_over(mut self, depth: u16) -> Self {
        let mut constant_abstactor = ConstantAbstractor::new(depth);
        self.initial_condition = self
            .initial_condition
            .accept(&mut constant_abstactor)
            .unwrap();
        self.transition_condition = self
            .transition_condition
            .accept(&mut constant_abstactor)
            .unwrap();
        self.property_condition = self
            .property_condition
            .accept(&mut constant_abstactor)
            .unwrap();

        self.state_variables
            .append(&mut constant_abstactor.variables());
        self.transition_condition =
            constant_abstactor.transition_properties(self.transition_condition);
        self.property_condition = constant_abstactor.invariant_properties(self.property_condition);
        // println!(
        //     "decl:\n  {}",
        //     self.state_variables
        //         .iter()
        //         .map(|x| format!("{} -> {} [{}]", x.current, x.next, x.relationship))
        //         .collect::<Vec<_>>()
        //         .join("  \n")
        // );
        // println!("init: {}", self.initial_condition);
        // println!("tran: {}", self.transition_condition);
        // println!("prop: {}", self.property_condition);

        self
    }

    pub fn unroll(&self, length: u16) -> SMTProblem {
        let mut builder = BMCBuilder {
            visitor: SyntaxBuilder,
            current_variables: self.get_all_current_variable_names(),
            next_variables: self.get_next_to_current_varible_names(),
            depth: 0,
            width: None,
        };
        let mut smt_problem = SMTProblem::new(&self.sorts, &self.function_definitions);

        smt_problem.add_assertion(&self.initial_condition, &mut builder);
        for _ in 0..length {
            // Must add variable definitions for each variable at each time step.
            smt_problem.add_variable_definitions(
                &self.state_variables,
                &self.actions,
                &mut builder,
            );
            smt_problem.add_assertion(&self.transition_condition, &mut builder);
            builder.add_step();
        }
        // Don't forget the variable definitions at time `length`.
        smt_problem.add_variable_definitions(&self.state_variables, &self.actions, &mut builder);
        smt_problem.add_property_assertion(&self.property_condition, &mut builder);
        assert!(
            smt_problem.init_and_trans_length() == (length + 1).into(),
            "Unrolling gives incorrect number of steps {} for length {}.",
            smt_problem.init_and_trans_length(),
            length
        );
        smt_problem
    }

    pub fn get_initial_condition_for_yardbird(&self) -> Term {
        self.unwrap_attributes(&self.initial_condition)
    }

    pub fn get_trans_condition_for_yardbird(&self) -> Term {
        self.unwrap_attributes(&self.transition_condition)
    }

    pub fn get_property_for_yardbird(&self) -> Term {
        self.unwrap_attributes(&self.property_condition)
    }

    fn unwrap_attributes(&self, attribute_term: &Term) -> Term {
        match attribute_term {
            Term::Attributes {
                term,
                attributes: _,
            } => LetExtract::substitute(*term.clone()),
            _ => panic!("Ill-formatted VMT condition: {}", self.initial_condition),
        }
    }

    pub fn get_initial_term(&self) -> SMTProblem {
        let mut builder = BMCBuilder {
            visitor: SyntaxBuilder,
            current_variables: self.get_all_current_variable_names(),
            next_variables: self.get_next_to_current_varible_names(),
            depth: 0,
            width: None,
        };
        let mut smt_problem = SMTProblem::new(&self.sorts, &self.function_definitions);
        smt_problem.add_variable_definitions(&self.state_variables, &self.actions, &mut builder);
        smt_problem.add_assertion(&self.initial_condition, &mut builder);
        smt_problem
    }

    pub fn get_trans_term(&self) -> SMTProblem {
        let mut builder = BMCBuilder {
            visitor: SyntaxBuilder,
            current_variables: self.get_all_current_variable_names(),
            next_variables: self.get_next_to_current_varible_names(),
            depth: 0,
            width: None,
        };
        let mut smt_problem = SMTProblem::new(&self.sorts, &self.function_definitions);

        for _ in 0..1 {
            // Must add variable definitions for each variable at each time step.
            smt_problem.add_variable_definitions(
                &self.state_variables,
                &self.actions,
                &mut builder,
            );
            smt_problem.add_assertion(&self.transition_condition, &mut builder);
            builder.add_step();
        }
        // Don't forget the variable definitions at time `length`.
        smt_problem.add_variable_definitions(&self.state_variables, &self.actions, &mut builder);
        smt_problem
    }

    pub fn get_property_term(&self) -> SMTProblem {
        let mut builder = BMCBuilder {
            visitor: SyntaxBuilder,
            current_variables: self.get_all_current_variable_names(),
            next_variables: self.get_next_to_current_varible_names(),
            depth: 0,
            width: None,
        };
        let mut smt_problem = SMTProblem::new(&self.sorts, &self.function_definitions);
        smt_problem.add_variable_definitions(&self.state_variables, &self.actions, &mut builder);
        smt_problem.add_property_assertion(&self.property_condition, &mut builder);
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
        info!("Number of Variables: {}", self.state_variables.len());
        info!("Number of Actions: {}", self.actions.len());
        info!("Number of Sorts: {}", self.sorts.len());
    }

    pub fn as_vmt_string(&self) -> String {
        self.as_commands()
            .iter()
            .map(|command| format!("{}", command.clone().accept(&mut SyntaxBuilder).unwrap()))
            .join("\n")
    }

    pub fn get_all_current_variable_names(&self) -> Vec<String> {
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

    pub fn get_next_to_current_varible_names(&self) -> HashMap<String, String> {
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

    #[allow(unused)]
    fn get_current_to_next_varible_names(&self) -> HashMap<String, String> {
        self.state_variables
            .iter()
            .map(|var| {
                (
                    var.get_current_variable_name().clone(),
                    var.get_next_variable_name().clone(),
                )
            })
            .collect()
    }

    pub fn add_instantiation(&mut self, term: &Term) -> bool {
        debug!("ADDED INSTANCE TO VMTModel: {}", term);
        self.initial_condition =
            self.add_instantiation_to_condition(term.clone(), self.initial_condition.clone());
        self.transition_condition =
            self.add_instantiation_to_condition(term.clone(), self.transition_condition.clone());
        true
    }

    pub fn get_parametric_sort_names(&self) -> Vec<String> {
        self.sorts
            .iter()
            .map(|sort| match sort {
                Command::DeclareSort { symbol, arity: _ } => symbol.0.clone(),
                _ => panic!("Sort in VMTModel is not of type DefineSort!: {}", sort),
            })
            .collect::<Vec<_>>()
    }

    pub fn get_state_holding_variables(&self) -> Vec<Variable> {
        let mut state_holding_variables = vec![];
        for state_variable in self.state_variables.clone() {
            // TODO: make this more principled by checking which variables occur as "next"
            let var_name = state_variable.get_current_variable_name();
            if var_name.contains("fml") || var_name.starts_with("__") {
                // Do not include formal arguments in state holding variables.
                continue;
            }
            state_holding_variables.push(state_variable);
        }
        state_holding_variables
    }

    fn add_instantiation_to_condition(&self, instantiation: Term, condition: Term) -> Term {
        let (term, attributes) = match condition {
            Term::Attributes { term, attributes } => (term, attributes),
            _ => panic!("Condition is not an Attributes: {}", condition),
        };
        let mut and_terms = get_and_terms(term);
        and_terms.push(instantiation.clone());
        Term::Attributes {
            term: Box::new(Term::Application {
                qual_identifier: crate::concrete::QualIdentifier::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("and".to_string()),
                    },
                },
                arguments: and_terms,
            }),
            attributes,
        }
    }

    pub fn write_vmt_out(&self, filename_opt: Option<String>) {
        let filename = match filename_opt {
            Some(fname) => fname,
            None => "out.vmt".into(),
        };
        log::info!("creating: {filename}");
        let mut file = File::create(filename).unwrap();

        let _ = file.write(self.as_vmt_string().as_bytes()).unwrap();
    }

    pub fn get_function_definitions(&self) -> Vec<Command> {
        self.function_definitions.clone()
    }
}

mod test {
    #[allow(unused_imports)]
    use super::*;

    #[test]
    fn test_double_abstract() {
        let vmt_model = VMTModel::from_path("./examples/array_copy.vmt").unwrap();
        let abstracted_model = vmt_model.abstract_array_theory();
        let abstracted_abstracted_model = abstracted_model.abstract_array_theory();

        assert_eq!(
            abstracted_model.as_vmt_string(),
            abstracted_abstracted_model.as_vmt_string(),
        );
    }
}
