use std::collections::HashMap;

use num::{BigUint, Zero};

use crate::concrete::{Command, Identifier, Sort, Symbol, SyntaxBuilder, Term};

use super::{type_checker::TypeChecker, utils::simple_identifier_with_name};

/// Rewrites Commands to use uninterpreted functions instead of explicit Arrays.
/// Currently turns all Arrays into Arr-Int-Int, but will be extended to arbitrary
/// Arrays later.
#[derive(Clone, Default)]
pub struct ArrayAbstractor {
    pub visitor: SyntaxBuilder,
    /// maps array names -> array + index types
    array_types: HashMap<String, (String, String)>,
    checker: TypeChecker,
}

impl ArrayAbstractor {
    pub(crate) fn get_array_type_definitions(&self) -> Vec<Command> {
        println!("{:#?}", self.array_types);
        self.array_types
            .values()
            .flat_map(|(index, value)| {
                let arr_sort = Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol(format!("Array-{}-{}", index, value)),
                    },
                };
                let index_sort = Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol(index.to_string()),
                    },
                };
                let value_sort = Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol(value.to_string()),
                    },
                };
                let sort_definition = Command::DeclareSort {
                    symbol: Symbol(format!("Array-{}-{}", index, value)),
                    arity: BigUint::zero(),
                };
                let read_definition: Command = Command::DeclareFun {
                    symbol: Symbol(format!("Read-{}-{}", index, value)),
                    parameters: vec![arr_sort.clone(), index_sort.clone()],
                    sort: value_sort.clone(),
                };
                let write_definition: Command = Command::DeclareFun {
                    symbol: Symbol(format!("Write-{}-{}", index, value)),
                    parameters: vec![arr_sort.clone(), index_sort.clone(), value_sort.clone()],
                    sort: arr_sort.clone(),
                };
                let constarr_definition: Command = Command::DeclareFun {
                    symbol: Symbol(format!("ConstArr-{}-{}", index, value)),
                    parameters: vec![value_sort],
                    sort: arr_sort,
                };
                vec![
                    sort_definition,
                    constarr_definition,
                    read_definition,
                    write_definition,
                ]
            })
            .collect()
    }
}

impl crate::rewriter::Rewriter for ArrayAbstractor {
    type V = SyntaxBuilder;
    type Error = crate::concrete::Error;

    fn visitor(&mut self) -> &mut Self::V {
        &mut self.visitor
    }

    fn visit_declare_fun(
        &mut self,
        symbol: <Self::V as crate::visitors::Smt2Visitor>::Symbol,
        parameters: Vec<<Self::V as crate::visitors::Smt2Visitor>::Sort>,
        sort: <Self::V as crate::visitors::Smt2Visitor>::Sort,
    ) -> Result<<Self::V as crate::visitors::Smt2Visitor>::Command, Self::Error> {
        let new_sort = match sort.clone() {
            crate::concrete::Sort::Simple { identifier: _ } => sort,
            crate::concrete::Sort::Parameterized {
                identifier,
                parameters,
            } => {
                if identifier.to_string() == "Array" {
                    // TODO: also need to have a better way of finding Sort names.
                    let (index_type, value_type) =
                        (parameters[0].to_string(), parameters[1].to_string());
                    self.array_types
                        .insert(symbol.0.clone(), (index_type.clone(), value_type.clone()));
                    self.checker.add_var(
                        symbol.0.clone(),
                        format!("{}-{}", index_type.clone(), value_type.clone()),
                    );
                    crate::concrete::Sort::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol(format!("Array-{}-{}", index_type, value_type)),
                        },
                    }
                } else {
                    sort
                }
            }
        };
        Ok(Command::DeclareFun {
            symbol,
            parameters,
            sort: new_sort,
        })
    }

    /// TODO: here's where the real problem of adding different theories comes in.
    /// Need to check the types of the arguments before getting the name of the
    /// identifier...
    fn visit_application(
        &mut self,
        qual_identifier: <Self::V as crate::visitors::Smt2Visitor>::QualIdentifier,
        arguments: Vec<<Self::V as crate::visitors::Smt2Visitor>::Term>,
    ) -> Result<<Self::V as crate::visitors::Smt2Visitor>::Term, Self::Error> {
        let new_identifier = match qual_identifier.clone() {
            crate::concrete::QualIdentifier::Simple { identifier } => {
                if identifier.to_string() == "select" {
                    println!("args: {qual_identifier} {arguments:#?}");
                    let type_name = self.checker.check(&arguments[0]).unwrap();
                    println!("type context: {:#?}", self.checker);
                    println!("type: {type_name}");
                    let (index, value) = &self.array_types[&arguments[0].to_string()];
                    simple_identifier_with_name(&format!("Read-{index}-{value}"))
                    // simple_identifier_with_name("Read-Int-Int")
                } else if identifier.to_string() == "store" {
                    simple_identifier_with_name("Write-Int-Int")
                } else {
                    qual_identifier
                }
            }
            crate::concrete::QualIdentifier::Sorted {
                identifier,
                sort: _,
            } => {
                if identifier.to_string() == "const" {
                    simple_identifier_with_name("ConstArr-Int-Int")
                } else {
                    qual_identifier
                }
            }
        };
        Ok(Term::Application {
            qual_identifier: new_identifier,
            arguments,
        })
    }
}
