use std::collections::HashMap;

use crate::concrete::{Command, Identifier, Term};

use super::{action::Action, axiom::Axiom, variable::Variable};

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

pub fn get_variables_actions_and_axioms(
    variable_relationships: Vec<&Command>,
    variable_commands: HashMap<String, Command>,
) -> (Vec<Variable>, Vec<Action>, Vec<Axiom>) {
    let mut state_variables: Vec<Variable> = vec![];
    let mut actions: Vec<Action> = vec![];
    let mut axioms: Vec<Axiom> = vec![];
    for variable_relationship in variable_relationships {
        match variable_relationship {
            Command::DefineFun { sig: _, term } => match term {
                Term::Attributes { term, attributes } => {
                    assert!(attributes.len() == 1);
                    let (keyword, value) = &attributes[0];
                    let keyword_string = keyword.to_string();
                    if keyword_string == ":next" {
                        let variable_command = get_variable_command(
                            scrub_variable_name(term.to_string()),
                            &variable_commands,
                        );
                        let new_variable_command = get_variable_command(
                            scrub_variable_name(value.to_string()),
                            &variable_commands,
                        );
                        state_variables.push(Variable {
                            current: variable_command,
                            next: new_variable_command,
                            relationship: variable_relationship.clone(),
                        });
                    } else if keyword_string == ":action" {
                        let action_variable_name = scrub_variable_name(term.to_string());
                        if variable_commands.contains_key(&action_variable_name) {
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
    (state_variables, actions, axioms)
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

pub fn get_transition_system_component(command: &Command, attribute: &str) -> Term {
    if command_has_attribute_string(command, attribute) {
        match command {
            Command::DefineFun { sig: _, term } => match term {
                Term::Attributes { term, attributes } => {
                    if attributes[0].0 .0 != attribute {
                        panic!(
                            "Ill-formed system component: {}.\nShould have {} as attribute.",
                            command, attribute
                        );
                    }
                    Term::Attributes {
                        term: term.clone(),
                        attributes: attributes.clone(),
                    }
                }
                _ => panic!("{}: Must have attribute.", attribute),
            },
            _ => panic!("{}: Command must be define-fun", attribute),
        }
    } else {
        panic!(
            "Initial, transition, and property commands must be the final three commands in the file.\nIll-formed system component: {}.\nShould have {} as attribute.",
            command, attribute
        );
    }
}

pub fn command_has_attribute_string(command: &Command, attribute: &str) -> bool {
    match command {
        Command::DefineFun {
            sig: _,
            term:
                Term::Attributes {
                    term: _,
                    attributes,
                },
        } => {
            assert!(attributes.len() == 1);
            let keyword = &attributes[0].0 .0;
            keyword == attribute
        }
        _ => false,
    }
}
