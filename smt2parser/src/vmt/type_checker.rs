use std::{collections::HashMap, fmt::Display};

use crate::concrete::Term;

#[derive(Debug)]
pub enum TypeError {
    UnknownIdentifier(String),
    MalformedType(String),
}

impl Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeError::UnknownIdentifier(ident) => write!(f, "Unknown identifier: {ident}"),
            TypeError::MalformedType(typ) => write!(f, "Malformed type: {typ}"),
        }
    }
}

impl std::error::Error for TypeError {}

pub type Result<T> = std::result::Result<T, TypeError>;

#[derive(Default, Debug, Clone)]
pub struct TypeChecker {
    /// Maps variables names to type names
    context: HashMap<String, String>,
}

impl TypeChecker {
    pub fn add_var(&mut self, var_name: String, type_name: String) {
        self.context.insert(var_name, type_name);
    }

    pub fn check(&self, term: &Term) -> Result<String> {
        match term {
            Term::Constant(_) => todo!(),
            Term::QualIdentifier(ident) => self
                .context
                .get(&ident.to_string())
                .cloned()
                .ok_or(TypeError::UnknownIdentifier(ident.to_string())),
            Term::Application {
                qual_identifier,
                arguments: _,
            } => {
                // getting the type from the string is a bit hacky, but will have to do for now
                let mut ident = qual_identifier.to_string();
                if ident.starts_with("|") {
                    ident = ident
                        .strip_prefix("|")
                        .unwrap()
                        .strip_suffix("|")
                        .unwrap()
                        .to_string();
                }
                println!("raw: {}", ident);
                let (_rest, return_type) = ident
                    .rsplit_once("-")
                    .ok_or(TypeError::MalformedType(ident.to_string()))?;
                println!("ret: {return_type}");
                if return_type.starts_with("(") {
                    Ok(return_type
                        .strip_prefix("(")
                        .unwrap()
                        .strip_suffix(")")
                        .unwrap()
                        .replace(" ", "-"))
                } else {
                    Ok(return_type.to_string())
                }
            }
            Term::Let {
                var_bindings: _,
                term: _,
            } => todo!(),
            Term::Forall { vars: _, term: _ } => todo!(),
            Term::Exists { vars: _, term: _ } => todo!(),
            Term::Match { term: _, cases: _ } => todo!(),
            Term::Attributes {
                term: _,
                attributes: _,
            } => todo!(),
        }
    }
}
