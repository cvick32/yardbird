use std::collections::{HashMap, HashSet};

use num::{BigUint, Zero};

use crate::concrete::{Command, Identifier, Sort, Symbol, SyntaxBuilder, Term};
use crate::visitors::Index;

use super::utils::simple_identifier_with_name;

/// Rewrites Commands to use uninterpreted functions instead of explicit Arrays.
#[derive(Clone)]
pub struct ArrayAbstractor {
    pub visitor: SyntaxBuilder,
    pub array_types: HashSet<(String, String)>,
    pub variable_types: HashMap<String, (String, String)>,
}

impl Default for ArrayAbstractor {
    fn default() -> Self {
        Self {
            visitor: SyntaxBuilder,
            array_types: HashSet::new(),
            variable_types: HashMap::new(),
        }
    }
}

/// Convert a stringified sort name back to a proper Sort object.
/// Handles indexed sorts like "BitVec32" -> (_ BitVec 32)
pub fn string_to_sort(name: &str) -> Sort {
    // Check for BitVec pattern: "BitVec" followed by a number
    if let Some(suffix) = name.strip_prefix("BitVec") {
        if let Ok(width) = suffix.parse::<u64>() {
            return Sort::Simple {
                identifier: Identifier::Indexed {
                    symbol: Symbol("BitVec".to_string()),
                    indices: vec![Index::Numeral(BigUint::from(width))],
                },
            };
        }
    }

    // Default: treat as a simple sort (Int, Bool, Real, or user-defined)
    Sort::Simple {
        identifier: Identifier::Simple {
            symbol: Symbol(name.to_string()),
        },
    }
}

impl ArrayAbstractor {
    pub fn get_array_type_definitions(&self) -> Vec<Command> {
        let mut commands = vec![];
        for (index, value) in &self.array_types {
            let arr_sort = Sort::Simple {
                identifier: Identifier::Simple {
                    symbol: Symbol(format!("Array_{index}_{value}")),
                },
            };
            // Convert stringified sort names back to proper Sort objects
            let index_sort = string_to_sort(index);
            let value_sort = string_to_sort(value);

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

    fn get_variable_type_from_term(&self, term: &Term) -> Option<(String, String)> {
        match term {
            Term::QualIdentifier(qual_id) => {
                let var_name = qual_id.get_name();
                self.variable_types.get(&var_name).cloned()
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
                        if name.starts_with("Read_") {
                            let parts: Vec<&str> = name.split('_').collect();
                            if parts.len() >= 3 {
                                let value_sort = parts[2..].join("_");
                                if value_sort.starts_with("Array_") {
                                    let array_parts: Vec<&str> =
                                        value_sort.splitn(3, '_').collect();
                                    if array_parts.len() == 3 {
                                        return Some((
                                            array_parts[1].to_string(),
                                            array_parts[2].to_string(),
                                        ));
                                    }
                                }
                            }
                        } else if name.starts_with("Write_") || name.starts_with("ConstArr_") {
                            let parts: Vec<&str> = name.split('_').collect();
                            if parts.len() >= 3 {
                                let index_sort = parts[1].to_string();
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

    fn convert_sort_to_abstracted(&mut self, sort: &Sort) -> Sort {
        match sort {
            crate::concrete::Sort::Simple { identifier: _ } => sort.clone(),
            crate::concrete::Sort::Parameterized {
                identifier,
                parameters,
            } => {
                if identifier.to_string() == "Array" {
                    let index_type = self.sort_to_string(&parameters[0]);
                    let value_type = self.sort_to_string(&parameters[1]);
                    self.array_types
                        .insert((index_type.clone(), value_type.clone()));
                    crate::concrete::Sort::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol(format!("Array_{index_type}_{value_type}")),
                        },
                    }
                } else {
                    sort.clone()
                }
            }
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
        if parameters.is_empty() {
            if let Some((index_sort, value_sort)) = self.extract_array_sorts_from_sort(&sort) {
                self.variable_types
                    .insert(symbol.0.clone(), (index_sort, value_sort));
            }
        }

        let new_parameters: Vec<_> = parameters
            .iter()
            .map(|param_sort| self.convert_sort_to_abstracted(param_sort))
            .collect();

        let new_sort = self.convert_sort_to_abstracted(&sort);

        Ok(Command::DeclareFun {
            symbol,
            parameters: new_parameters,
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
                    let array_type =
                        if let Some(types) = self.get_variable_type_from_term(&arguments[0]) {
                            Some(types)
                        } else {
                            self.extract_array_type_from_term(&arguments[0])
                        };

                    if let Some((index_sort, value_sort)) = array_type {
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
                    let array_type =
                        if let Some(types) = self.get_variable_type_from_term(&arguments[0]) {
                            Some(types)
                        } else {
                            self.extract_array_type_from_term(&arguments[0])
                        };

                    if let Some((index_sort, value_sort)) = array_type {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::concrete::{Command, Identifier, Sort, Symbol};
    use crate::rewriter::Rewriter;

    #[test]
    fn test_sort_to_string_simple() {
        let abstractor = ArrayAbstractor::default();

        // Test simple sort
        let int_sort = Sort::Simple {
            identifier: Identifier::Simple {
                symbol: Symbol("Int".to_string()),
            },
        };
        assert_eq!(abstractor.sort_to_string(&int_sort), "Int");
    }

    #[test]
    fn test_sort_to_string_simple_array() {
        let abstractor = ArrayAbstractor::default();

        // Test simple array: (Array Int Int)
        let array_sort = Sort::Parameterized {
            identifier: Identifier::Simple {
                symbol: Symbol("Array".to_string()),
            },
            parameters: vec![
                Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Int".to_string()),
                    },
                },
                Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Int".to_string()),
                    },
                },
            ],
        };
        assert_eq!(abstractor.sort_to_string(&array_sort), "Array_Int_Int");
    }

    #[test]
    fn test_sort_to_string_nested_array() {
        let abstractor = ArrayAbstractor::default();

        // Test nested array: (Array Int (Array Int Int))
        let inner_array = Sort::Parameterized {
            identifier: Identifier::Simple {
                symbol: Symbol("Array".to_string()),
            },
            parameters: vec![
                Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Int".to_string()),
                    },
                },
                Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Int".to_string()),
                    },
                },
            ],
        };

        let outer_array = Sort::Parameterized {
            identifier: Identifier::Simple {
                symbol: Symbol("Array".to_string()),
            },
            parameters: vec![
                Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Int".to_string()),
                    },
                },
                inner_array,
            ],
        };

        assert_eq!(
            abstractor.sort_to_string(&outer_array),
            "Array_Int_Array_Int_Int"
        );
    }

    #[test]
    fn test_abstraction_nested_array_variable() {
        let mut abstractor = ArrayAbstractor::default();

        // Test: (declare-fun a () (Array Int (Array Int Int)))
        let inner_array = Sort::Parameterized {
            identifier: Identifier::Simple {
                symbol: Symbol("Array".to_string()),
            },
            parameters: vec![
                Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Int".to_string()),
                    },
                },
                Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Int".to_string()),
                    },
                },
            ],
        };

        let outer_array = Sort::Parameterized {
            identifier: Identifier::Simple {
                symbol: Symbol("Array".to_string()),
            },
            parameters: vec![
                Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Int".to_string()),
                    },
                },
                inner_array,
            ],
        };

        let result = abstractor.visit_declare_fun(Symbol("a".to_string()), vec![], outer_array);

        assert!(result.is_ok());
        let abstracted = result.unwrap();

        // Should produce: (declare-fun a () Array_Int_Array_Int_Int)
        match abstracted {
            Command::DeclareFun {
                symbol,
                parameters,
                sort,
            } => {
                assert_eq!(symbol.0, "a");
                assert!(parameters.is_empty());
                assert_eq!(sort.to_string(), "Array_Int_Array_Int_Int");
            }
            _ => panic!("Expected DeclareFun"),
        }

        // Should register both array types
        assert!(abstractor
            .array_types
            .contains(&("Int".to_string(), "Array_Int_Int".to_string())));
    }

    #[test]
    fn test_abstraction_function_with_nested_array_params() {
        let mut abstractor = ArrayAbstractor::default();

        // Test: (declare-fun f ((Array Int Int)) Int)
        let array_param = Sort::Parameterized {
            identifier: Identifier::Simple {
                symbol: Symbol("Array".to_string()),
            },
            parameters: vec![
                Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Int".to_string()),
                    },
                },
                Sort::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("Int".to_string()),
                    },
                },
            ],
        };

        let int_sort = Sort::Simple {
            identifier: Identifier::Simple {
                symbol: Symbol("Int".to_string()),
            },
        };

        let result = abstractor.visit_declare_fun(
            Symbol("f".to_string()),
            vec![array_param],
            int_sort.clone(),
        );

        assert!(result.is_ok());
        let abstracted = result.unwrap();

        // Should produce: (declare-fun f (Array_Int_Int) Int)
        match abstracted {
            Command::DeclareFun {
                symbol,
                parameters,
                sort,
            } => {
                assert_eq!(symbol.0, "f");
                assert_eq!(parameters.len(), 1);
                assert_eq!(parameters[0].to_string(), "Array_Int_Int");
                assert_eq!(sort.to_string(), "Int");
            }
            _ => panic!("Expected DeclareFun"),
        }

        // Should register the array type
        assert!(abstractor
            .array_types
            .contains(&("Int".to_string(), "Int".to_string())));
    }
}
