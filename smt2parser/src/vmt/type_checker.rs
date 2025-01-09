use std::{collections::HashMap, fmt::Display};

use crate::concrete::{Identifier, Sort, Symbol, Term};

#[derive(Debug, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VmtType {
    Array {
        index: Box<VmtType>,
        value: Box<VmtType>,
    },
    Int,
    Unknown(String),
}

#[derive(Default, Debug, Clone)]
pub struct TypeChecker {
    /// Maps variables names to type names
    context: HashMap<String, VmtType>,
}

impl TypeChecker {
    pub fn insert(&mut self, var_name: impl ToString, vmt_type: impl Into<VmtType>) {
        self.context.insert(var_name.to_string(), vmt_type.into());
    }

    pub fn check(&self, term: &Term) -> Result<VmtType> {
        match term {
            Term::Constant(_) => todo!(),
            Term::QualIdentifier(ident) => self
                .context
                .get(&ident.to_string())
                .cloned()
                .ok_or(TypeError::UnknownIdentifier(ident.to_string())),
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                let ident = qual_identifier.to_string();
                match ident.as_str() {
                    id if id.contains("Read") || id == "select" => {
                        let array = &arguments[0];
                        let _index = &arguments[1];
                        if let VmtType::Array { value, .. } = self.check(array)? {
                            Ok(*value)
                        } else {
                            Err(TypeError::MalformedType("".to_string()))
                        }
                    }
                    id if id.contains("Write") || id == "store" => self.check(&arguments[0]),
                    _ => Err(TypeError::UnknownIdentifier(ident.to_string())),
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

impl From<Sort> for VmtType {
    fn from(value: Sort) -> Self {
        match value {
            Sort::Simple { identifier } => {
                let ident = identifier.to_string();
                match ident.as_str() {
                    "Int" => VmtType::Int,
                    _ => VmtType::Unknown(ident),
                }
            }
            Sort::Parameterized {
                identifier,
                mut parameters,
            } if identifier.to_string() == "Array" && parameters.len() == 2 => {
                let index = parameters.pop().unwrap();
                let value = parameters.pop().unwrap();
                VmtType::Array {
                    index: Box::new(value.into()),
                    value: Box::new(index.into()),
                }
            }
            x => VmtType::Unknown(x.to_string()),
        }
    }
}

impl VmtType {
    pub fn to_abstract_sort(&self) -> Sort {
        Sort::Simple {
            identifier: Identifier::Simple {
                symbol: Symbol(self.to_abstract_string()),
            },
        }
    }

    pub fn to_abstract_string(&self) -> String {
        match self {
            VmtType::Array { index, value } => format!(
                "Array-{}-{}",
                index.to_abstract_string(),
                if value.is_complex() {
                    format!("({})", value.to_abstract_string())
                } else {
                    value.to_abstract_string()
                }
            ),
            VmtType::Int => "Int".to_string(),
            VmtType::Unknown(x) => x.to_string(),
        }
    }

    pub fn is_complex(&self) -> bool {
        match self {
            VmtType::Array { .. } => true,
            VmtType::Int => false,
            VmtType::Unknown(_) => false,
        }
    }
}
