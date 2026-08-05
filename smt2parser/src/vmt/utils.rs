use std::collections::{hash_map::Entry, HashMap, HashSet};

use crate::concrete::{Command, Identifier, QualIdentifier, Symbol, Term};

use super::{action::Action, axiom::Axiom, variable::Variable};

static BOOLEAN_CONNECTIVES: [&str; 4] = ["and", "or", "=>", "="];

pub fn simple_identifier_with_name(name: &str) -> QualIdentifier {
    crate::concrete::QualIdentifier::Simple {
        identifier: Identifier::Simple {
            symbol: Symbol(name.to_string()),
        },
    }
}

pub fn is_boolean_connective(qual_identifier: &QualIdentifier) -> bool {
    BOOLEAN_CONNECTIVES.contains(&qual_identifier.get_name().as_str())
}

/// Only call this method if you're sure that the given Term is or should be
/// an `and` Application. It will panic if not.
pub fn get_and_terms(term: Box<Term>) -> Vec<Term> {
    match *term.clone() {
        Term::Application {
            qual_identifier,
            arguments,
        } => match qual_identifier {
            crate::concrete::QualIdentifier::Simple { identifier } => match identifier {
                Identifier::Simple { symbol } => {
                    if symbol.0 == "and" {
                        arguments
                    } else {
                        panic!("Inner term of condition is not `and` Application: {}", term)
                    }
                }
                Identifier::Indexed {
                    symbol: _,
                    indices: _,
                } => panic!("Inner term of condition is not `and` Application: {}", term),
            },
            crate::concrete::QualIdentifier::Sorted {
                identifier: _,
                sort: _,
            } => todo!(),
        },
        _ => panic!("Inner term of condition is not Application: {}", term),
    }
}

pub struct ClassifiedVariables {
    pub state_variables: Vec<Variable>,
    pub input_variables: Vec<Command>,
    pub actions: Vec<Action>,
    pub axioms: Vec<Axiom>,
}

pub fn classify_variables(
    variable_relationships: Vec<Command>,
    mut variable_commands: HashMap<String, Command>,
    declaration_order: Vec<String>,
) -> ClassifiedVariables {
    let mut state_variables: Vec<Variable> = vec![];
    let mut actions: Vec<Action> = vec![];
    let mut axioms: Vec<Axiom> = vec![];
    let mut classified_names = HashSet::new();
    for variable_relationship in &variable_relationships {
        match variable_relationship {
            Command::DefineFun { sig: _, term } => match term {
                Term::Attributes { term, attributes } => {
                    assert!(attributes.len() == 1);
                    let (keyword, value) = &attributes[0];
                    let keyword_string = keyword.to_string();
                    if keyword_string == ":next" {
                        let current_name = scrub_variable_name(term.to_string());
                        let next_name = scrub_variable_name(value.to_string());
                        let variable_command =
                            get_variable_command(current_name.clone(), &variable_commands);
                        let new_variable_command = get_or_create_next_variable_command(
                            next_name.clone(),
                            &variable_command,
                            &mut variable_commands,
                        );
                        classified_names.insert(current_name);
                        classified_names.insert(next_name);
                        state_variables.push(Variable {
                            current: variable_command,
                            next: new_variable_command,
                            relationship: variable_relationship.clone(),
                        });
                    } else if keyword_string == ":action" {
                        let action_variable_name = scrub_variable_name(term.to_string());
                        if variable_commands.contains_key(&action_variable_name) {
                            classified_names.insert(action_variable_name.clone());
                            for (variable_name, action_command) in &variable_commands {
                                if action_variable_name == *variable_name {
                                    actions.push(Action {
                                        action: action_command.clone(),
                                        relationship: variable_relationship.clone(),
                                    });
                                    break;
                                }
                            }
                        } else {
                            panic!("Proposed action variable {} not previously defined.", term);
                        }
                    } else if keyword_string == ":axiom" {
                        axioms.push(Axiom {
                            _axiom: *term.clone(),
                        });
                    } else {
                        panic!("Only `next` and `action` keyword attributes are allowed in variable relationships found: {}", keyword_string);
                    }
                }
                _ => panic!("Only Attribute terms can define variable relationships."),
            },
            _ => panic!("Variable Relationship is not a (define-fun)."),
        }
    }

    let input_variables = declaration_order
        .into_iter()
        .filter(|name| !classified_names.contains(name))
        .filter_map(|name| variable_commands.get(&name).cloned())
        .collect();

    ClassifiedVariables {
        state_variables,
        input_variables,
        actions,
        axioms,
    }
}

fn get_or_create_next_variable_command(
    variable_name: String,
    current_variable_command: &Command,
    variable_commands: &mut HashMap<String, Command>,
) -> Command {
    match variable_commands.entry(variable_name.clone()) {
        Entry::Occupied(entry) => entry.get().clone(),
        Entry::Vacant(entry) => {
            let Command::DeclareFun {
                symbol: _,
                parameters,
                sort,
            } = current_variable_command
            else {
                panic!("Current state variable must be declared with declare-fun")
            };
            let command = Command::DeclareFun {
                symbol: Symbol(variable_name),
                parameters: parameters.clone(),
                sort: sort.clone(),
            };
            entry.insert(command.clone());
            command
        }
    }
}

pub fn scrub_variable_name(variable_name: String) -> String {
    if variable_name.starts_with("|") && variable_name.ends_with("|") {
        let mut chars = variable_name.chars();
        chars.next();
        chars.next_back();
        chars.as_str().to_string()
    } else {
        variable_name
    }
}

pub fn get_variable_command(
    variable_name: String,
    variable_commands: &HashMap<String, Command>,
) -> Command {
    match variable_commands.get(&variable_name) {
        Some(command) => command.clone(),
        None => panic!(
            "First term in define-fun must be a variable name: {}",
            variable_name
        ),
    }
}

pub fn get_annotated_term(command: &Command, attribute: &str) -> Option<Term> {
    match command {
        Command::DefineFun {
            sig: _,
            term: Term::Attributes { term, attributes },
        } => attributes
            .iter()
            .find(|(keyword, _)| keyword.0 == attribute)
            .map(|attribute| Term::Attributes {
                term: term.clone(),
                attributes: vec![attribute.clone()],
            }),
        _ => None,
    }
}
