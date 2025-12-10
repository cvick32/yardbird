use std::collections::HashSet;

use num::{BigUint, Zero};

use crate::concrete::{Command, Identifier, Sort, Symbol, SyntaxBuilder, Term};

use super::utils::simple_identifier_with_name;

/// Rewrites Commands to use uninterpreted functions instead of explicit Arrays.
#[derive(Clone)]
pub struct ArrayAbstractor {
    pub visitor: SyntaxBuilder,
    pub array_types: HashSet<(String, String)>,
}

impl Default for ArrayAbstractor {
    fn default() -> Self {
        Self {
            visitor: SyntaxBuilder,
            array_types: HashSet::new(),
        }
    }
}

impl ArrayAbstractor {
    pub(crate) fn get_array_type_definitions(&self) -> Vec<Command> {
        let mut commands = vec![];
        for (index, value) in &self.array_types {
            let arr_sort = Sort::Simple {
                identifier: Identifier::Simple {
                    symbol: Symbol(format!("Array_{index}_{value}")),
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
                symbol: Symbol(format!("Array_{index}_{value}")),
                arity: BigUint::zero(),
            };
            let read_definition: Command = Command::DeclareFun {
                symbol: Symbol(format!("Read_{index}_{value}")),
                parameters: vec![arr_sort.clone(), index_sort.clone()],
                sort: value_sort.clone(),
            };
            let write_definition: Command = Command::DeclareFun {
                symbol: Symbol(format!("Write_{index}_{value}")),
                parameters: vec![arr_sort.clone(), index_sort.clone(), value_sort.clone()],
                sort: arr_sort.clone(),
            };
            let constarr_definition: Command = Command::DeclareFun {
                symbol: Symbol(format!("ConstArr_{index}_{value}")),
                parameters: vec![value_sort],
                sort: arr_sort,
            };
            commands.push(sort_definition);
            commands.push(constarr_definition);
            commands.push(read_definition);
            commands.push(write_definition);
        }
        commands
    }

    /// Convert a Sort to a simplified string name (e.g., "Int", "BitVec32", "Array_Int_Int")
    /// For nested arrays like (Array Int (Array Int Int)), produces "Array_Int_Array_Int_Int"
    #[allow(clippy::only_used_in_recursion)]
    fn sort_to_string(&self, sort: &Sort) -> String {
        match sort {
            Sort::Simple { identifier } => match identifier {
                Identifier::Simple { symbol } => symbol.0.clone(),
                Identifier::Indexed { symbol, indices } => {
                    // For indexed identifiers like (_ BitVec 32), format as "BitVec32"
                    let indices_str = indices
                        .iter()
                        .map(|idx| match idx {
                            crate::visitors::Index::Numeral(n) => n.to_string(),
                            crate::visitors::Index::Symbol(s) => s.0.clone(),
                        })
                        .collect::<Vec<_>>()
                        .join("_");
                    format!("{}{}", symbol.0, indices_str)
                }
            },
            Sort::Parameterized {
                identifier,
                parameters,
            } => {
                // Include the parameterized type identifier (e.g., "Array") in the output
                // This ensures (Array Int Int) -> "Array_Int_Int" not just "Int_Int"
                let identifier_str = match identifier {
                    Identifier::Simple { symbol } => symbol.0.as_str(),
                    Identifier::Indexed { symbol, .. } => symbol.0.as_str(),
                };
                format!(
                    "{}_{}",
                    identifier_str,
                    parameters
                        .iter()
                        .map(|p| self.sort_to_string(p))
                        .collect::<Vec<_>>()
                        .join("_")
                )
            }
        }
    }

    /// Extract index and value sorts from an Array sort
    /// Returns (index_sort_name, value_sort_name)
    fn extract_array_sorts_from_sort(&self, sort: &Sort) -> Option<(String, String)> {
        match sort {
            Sort::Parameterized {
                identifier,
                parameters,
            } => {
                // Check if this is an Array sort
                let is_array = match identifier {
                    Identifier::Simple { symbol } => symbol.0 == "Array",
                    Identifier::Indexed { symbol, .. } => symbol.0 == "Array",
                };
                if is_array && parameters.len() == 2 {
                    Some((
                        self.sort_to_string(&parameters[0]),
                        self.sort_to_string(&parameters[1]),
                    ))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Extract array type from a term (by looking at variable declarations or other type info)
    /// This is a best-effort approach - we try to infer types from the structure
    /// Returns (index_sort_name, value_sort_name)
    fn extract_array_type_from_term(&self, term: &Term) -> Option<(String, String)> {
        match term {
            // If it's a qualified identifier with a sort annotation, use that
            Term::QualIdentifier(crate::concrete::QualIdentifier::Sorted {
                identifier: _,
                sort,
            }) => self.extract_array_sorts_from_sort(sort),
            // If it's an application, try to extract from the result type
            Term::Application {
                qual_identifier,
                arguments: _,
            } => {
                match qual_identifier {
                    crate::concrete::QualIdentifier::Sorted {
                        identifier: _,
                        sort,
                    } => self.extract_array_sorts_from_sort(sort),
                    crate::concrete::QualIdentifier::Simple { identifier } => {
                        // Try to infer from function name
                        let name = identifier.to_string();
                        if name.starts_with("Write_")
                            || name.starts_with("Read_")
                            || name.starts_with("ConstArr_")
                        {
                            // Parse the type suffix like "Write_BitVec5_BitVec32" or "Read_Int_Array_Int_Int"
                            // For nested arrays, we need to extract index and value carefully
                            // Format: Op_IndexSort_ValueSort where ValueSort might be Array_X_Y
                            let parts: Vec<&str> = name.split('_').collect();
                            if parts.len() >= 3 {
                                // Index is always parts[1]
                                let index_sort = parts[1].to_string();
                                // Value is everything after index, joined back
                                let value_sort = parts[2..].join("_");
                                return Some((index_sort, value_sort));
                            }
                        }
                        None
                    }
                }
            }
            _ => None,
        }
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
                        .insert((index_type.clone(), value_type.clone()));
                    crate::concrete::Sort::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol(format!("Array_{index_type}_{value_type}")),
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

    /// Implements type-aware abstraction of array operations.
    /// Extracts type information from arguments and generates typed function names.
    fn visit_application(
        &mut self,
        qual_identifier: <Self::V as crate::visitors::Smt2Visitor>::QualIdentifier,
        arguments: Vec<<Self::V as crate::visitors::Smt2Visitor>::Term>,
    ) -> Result<<Self::V as crate::visitors::Smt2Visitor>::Term, Self::Error> {
        let new_identifier = match qual_identifier.clone() {
            crate::concrete::QualIdentifier::Simple { identifier } => {
                if identifier.to_string() == "select" {
                    // select: (Array a b) a -> b
                    // Extract array type from first argument
                    if let Some((index_sort, value_sort)) =
                        self.extract_array_type_from_term(&arguments[0])
                    {
                        self.array_types
                            .insert((index_sort.clone(), value_sort.clone()));
                        simple_identifier_with_name(&format!("Read_{}_{}", index_sort, value_sort))
                    } else {
                        // Fallback to Int-Int if we can't determine the type
                        self.array_types
                            .insert(("Int".to_string(), "Int".to_string()));
                        simple_identifier_with_name("Read_Int_Int")
                    }
                } else if identifier.to_string() == "store" {
                    // store: (Array a b) a b -> (Array a b)
                    // Extract array type from first argument
                    if let Some((index_sort, value_sort)) =
                        self.extract_array_type_from_term(&arguments[0])
                    {
                        self.array_types
                            .insert((index_sort.clone(), value_sort.clone()));
                        simple_identifier_with_name(&format!("Write_{}_{}", index_sort, value_sort))
                    } else {
                        // Fallback to Int-Int
                        self.array_types
                            .insert(("Int".to_string(), "Int".to_string()));
                        simple_identifier_with_name("Write_Int_Int")
                    }
                } else {
                    qual_identifier
                }
            }
            crate::concrete::QualIdentifier::Sorted { identifier, sort } => {
                if identifier.to_string() == "const" {
                    // const is sorted with the Array type: (as const (Array a b))
                    if let Some((index_sort, value_sort)) =
                        self.extract_array_sorts_from_sort(&sort)
                    {
                        self.array_types
                            .insert((index_sort.clone(), value_sort.clone()));
                        simple_identifier_with_name(&format!(
                            "ConstArr_{}_{}",
                            index_sort, value_sort
                        ))
                    } else {
                        // Fallback to Int-Int
                        self.array_types
                            .insert(("Int".to_string(), "Int".to_string()));
                        simple_identifier_with_name("ConstArr_Int_Int")
                    }
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
