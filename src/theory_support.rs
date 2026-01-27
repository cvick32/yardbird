use std::vec;

use smt2parser::concrete::{Command, Identifier, QualIdentifier, Sort, Symbol, Term};
use smt2parser::vmt::array_abstractor::string_to_sort;
use smt2parser::vmt::VMTModel;

/// Trait for providing theory-specific function declarations and model abstractions
pub trait TheorySupport {
    /// Returns the list of uninterpreted functions that need to be declared in Z3
    fn get_uninterpreted_functions(&self) -> Vec<FunctionDeclaration>;

    /// Returns the list of axioms needed for this theory.
    fn get_axiom_formulas(&self) -> Vec<Command>;

    /// Returns the SMT logic string for this theory (e.g., "QF_LIA", "UFLIA")
    fn get_logic_string(&self) -> String;

    /// Abstracts the VMT model for this theory (replaces theory-specific operations with uninterpreted functions)
    fn abstract_model(&self, model: VMTModel) -> (VMTModel, Vec<(String, String)>);

    /// Returns true if this theory requires abstraction
    fn requires_abstraction(&self) -> bool;

    /// Returns true if this theory support uses quantified axioms
    /// (e.g., read-after-write axiom for arrays)
    fn uses_quantified_axioms(&self) -> bool {
        false // Default: no axioms
    }
}

/// A function declaration for Z3
#[derive(Debug, Clone)]
pub struct FunctionDeclaration {
    pub name: String,
    pub arg_sorts: Vec<Sort>,
    pub return_sort: Sort,
}

impl FunctionDeclaration {
    pub fn new(name: impl Into<String>, arg_sorts: Vec<Sort>, return_sort: Sort) -> Self {
        Self {
            name: name.into(),
            arg_sorts,
            return_sort,
        }
    }

    /// Convert to an SMT2 declare-fun command
    pub fn to_command(&self) -> Command {
        Command::DeclareFun {
            symbol: Symbol(self.name.clone()),
            parameters: self.arg_sorts.clone(),
            sort: self.return_sort.clone(),
        }
    }
}

/// Helper to create common sorts
pub fn int_sort() -> Sort {
    Sort::Simple {
        identifier: Identifier::Simple {
            symbol: Symbol("Int".to_string()),
        },
    }
}

pub fn bool_sort() -> Sort {
    Sort::Simple {
        identifier: Identifier::Simple {
            symbol: Symbol("Bool".to_string()),
        },
    }
}

pub fn list_sort(element_sort: &str) -> Sort {
    Sort::Simple {
        identifier: Identifier::Simple {
            symbol: Symbol(format!("List{}", element_sort)),
        },
    }
}

/// Theory support for list operations
#[derive(Clone)]
pub struct ListTheorySupport;

impl TheorySupport for ListTheorySupport {
    fn get_uninterpreted_functions(&self) -> Vec<FunctionDeclaration> {
        let list_int_sort = list_sort("Int");
        let int_sort = int_sort();
        let bool_sort = bool_sort();

        vec![
            // Basic constructors
            FunctionDeclaration::new("nil", vec![], list_int_sort.clone()),
            FunctionDeclaration::new(
                "cons",
                vec![int_sort.clone(), list_int_sort.clone()],
                list_int_sort.clone(),
            ),
            // Destructors
            FunctionDeclaration::new("head", vec![list_int_sort.clone()], int_sort.clone()),
            FunctionDeclaration::new("tail", vec![list_int_sort.clone()], list_int_sort.clone()),
            // Properties
            FunctionDeclaration::new("length", vec![list_int_sort.clone()], int_sort.clone()),
            FunctionDeclaration::new("is-nil", vec![list_int_sort.clone()], bool_sort),
            // Operations
            FunctionDeclaration::new(
                "append",
                vec![list_int_sort.clone(), list_int_sort.clone()],
                list_int_sort.clone(),
            ),
            FunctionDeclaration::new(
                "reverse",
                vec![list_int_sort.clone()],
                list_int_sort.clone(),
            ),
            FunctionDeclaration::new(
                "nth",
                vec![list_int_sort.clone(), int_sort.clone()],
                int_sort.clone(),
            ),
            FunctionDeclaration::new(
                "update-nth",
                vec![list_int_sort.clone(), int_sort.clone(), int_sort.clone()],
                list_int_sort.clone(),
            ),
        ]
    }

    fn get_logic_string(&self) -> String {
        "QF_LIA".to_string() // Quantifier-free linear integer arithmetic + uninterpreted functions
    }

    fn abstract_model(&self, model: VMTModel) -> (VMTModel, Vec<(String, String)>) {
        // For now, we don't need to abstract the model for lists since we're declaring them as uninterpreted
        // In the future, we could implement a ListAbstractor similar to ArrayAbstractor
        model.abstract_array_theory()
    }

    fn requires_abstraction(&self) -> bool {
        false // We declare functions directly rather than abstracting
    }

    fn get_axiom_formulas(&self) -> Vec<Command> {
        vec![]
    }
}

pub fn array_sort(index_sort: &str, element_sort: &str) -> Sort {
    Sort::Simple {
        identifier: Identifier::Simple {
            symbol: Symbol(format!("Array_{}_{}", index_sort, element_sort)),
        },
    }
}

#[derive(Clone)]
pub struct ArrayTheorySupport {
    /// Set of (index_sort, value_sort) pairs discovered during abstraction
    pub array_types: Vec<(String, String)>,
}

impl ArrayTheorySupport {
    pub fn new(array_types: Vec<(String, String)>) -> Self {
        Self { array_types }
    }
}

/// Check if any array type involves bitvectors
fn has_bitvector_types(array_types: &[(String, String)]) -> bool {
    array_types
        .iter()
        .any(|(idx, val)| idx.starts_with("BitVec") || val.starts_with("BitVec"))
}

pub fn get_uninterpreted_array_functions(
    array_types: &[(String, String)],
) -> Vec<FunctionDeclaration> {
    let mut functions = Vec::new();

    // Generate functions for each discovered array type
    for (index_sort, value_sort) in array_types {
        let array_sort_type = array_sort(index_sort, value_sort);
        // Use string_to_sort to handle indexed sorts like BitVec
        let index_sort_type = string_to_sort(index_sort);
        let value_sort_type = string_to_sort(value_sort);

        functions.push(FunctionDeclaration::new(
            format!("Read_{}_{}", index_sort, value_sort),
            vec![array_sort_type.clone(), index_sort_type.clone()],
            value_sort_type.clone(),
        ));

        functions.push(FunctionDeclaration::new(
            format!("Write_{}_{}", index_sort, value_sort),
            vec![
                array_sort_type.clone(),
                index_sort_type.clone(),
                value_sort_type.clone(),
            ],
            array_sort_type.clone(),
        ));

        functions.push(FunctionDeclaration::new(
            format!("ConstArr_{}_{}", index_sort, value_sort),
            vec![value_sort_type],
            array_sort_type,
        ));
    }

    functions
}

impl TheorySupport for ArrayTheorySupport {
    fn get_uninterpreted_functions(&self) -> Vec<FunctionDeclaration> {
        get_uninterpreted_array_functions(&self.array_types)
    }

    fn get_logic_string(&self) -> String {
        if has_bitvector_types(&self.array_types) {
            // Use AUFBV for arrays with bitvector indices or values
            // The UF is implicit in AUFBV (arrays + uninterpreted functions + bitvectors)
            "AUFBV".to_string()
        } else {
            "UFLIA".to_string()
        }
    }

    fn abstract_model(&self, model: VMTModel) -> (VMTModel, Vec<(String, String)>) {
        model.abstract_array_theory()
    }

    fn requires_abstraction(&self) -> bool {
        true
    }

    fn get_axiom_formulas(&self) -> Vec<Command> {
        vec![]
    }
}

#[derive(Clone)]
pub struct ArrayWithQuantifiersTheorySupport {
    pub array_types: Vec<(String, String)>,
}

impl ArrayWithQuantifiersTheorySupport {
    pub fn new(array_types: Vec<(String, String)>) -> Self {
        Self { array_types }
    }
}

impl TheorySupport for ArrayWithQuantifiersTheorySupport {
    fn get_uninterpreted_functions(&self) -> Vec<FunctionDeclaration> {
        get_uninterpreted_array_functions(&self.array_types)
    }

    fn get_logic_string(&self) -> String {
        if has_bitvector_types(&self.array_types) {
            // Use AUFBV for arrays with bitvector indices or values
            "AUFBV".to_string()
        } else {
            "UFLIA".to_string()
        }
    }

    fn abstract_model(&self, model: VMTModel) -> (VMTModel, Vec<(String, String)>) {
        model.abstract_array_theory()
    }

    fn requires_abstraction(&self) -> bool {
        true
    }

    fn get_axiom_formulas(&self) -> Vec<Command> {
        let mut axioms = Vec::new();

        for (index_sort, value_sort) in &self.array_types {
            axioms.push(generate_read_after_write_axiom(index_sort, value_sort));
            axioms.push(generate_write_preserves_other_axiom(index_sort, value_sort));
            axioms.push(generate_const_array_axiom(index_sort, value_sort));
        }

        axioms
    }

    fn uses_quantified_axioms(&self) -> bool {
        true
    }
}

fn generate_read_after_write_axiom(index_sort: &str, value_sort: &str) -> Command {
    let array_sort = string_to_sort(&format!("Array_{}_{}", index_sort, value_sort));
    let idx_sort = string_to_sort(index_sort);
    let val_sort = string_to_sort(value_sort);

    let read_fn = format!("Read_{}_{}", index_sort, value_sort);
    let write_fn = format!("Write_{}_{}", index_sort, value_sort);

    Command::Assert {
        term: Term::Forall {
            vars: vec![
                (Symbol("a".to_string()), array_sort.clone()),
                (Symbol("i".to_string()), idx_sort.clone()),
                (Symbol("j".to_string()), idx_sort.clone()),
                (Symbol("v".to_string()), val_sort.clone()),
            ],
            term: Box::new(Term::Application {
                qual_identifier: QualIdentifier::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("=>".to_string()),
                    },
                },
                arguments: vec![
                    // Condition: (= i j)
                    Term::Application {
                        qual_identifier: QualIdentifier::Simple {
                            identifier: Identifier::Simple {
                                symbol: Symbol("=".to_string()),
                            },
                        },
                        arguments: vec![
                            Term::QualIdentifier(QualIdentifier::Simple {
                                identifier: Identifier::Simple {
                                    symbol: Symbol("i".to_string()),
                                },
                            }),
                            Term::QualIdentifier(QualIdentifier::Simple {
                                identifier: Identifier::Simple {
                                    symbol: Symbol("j".to_string()),
                                },
                            }),
                        ],
                    },
                    // Consequence: (= (select (store a i v) j) v)
                    Term::Application {
                        qual_identifier: QualIdentifier::Simple {
                            identifier: Identifier::Simple {
                                symbol: Symbol("=".to_string()),
                            },
                        },
                        arguments: vec![
                            Term::Application {
                                qual_identifier: QualIdentifier::Simple {
                                    identifier: Identifier::Simple {
                                        symbol: Symbol(read_fn.clone()),
                                    },
                                },
                                arguments: vec![
                                    Term::Application {
                                        qual_identifier: QualIdentifier::Simple {
                                            identifier: Identifier::Simple {
                                                symbol: Symbol(write_fn),
                                            },
                                        },
                                        arguments: vec![
                                            Term::QualIdentifier(QualIdentifier::Simple {
                                                identifier: Identifier::Simple {
                                                    symbol: Symbol("a".to_string()),
                                                },
                                            }),
                                            Term::QualIdentifier(QualIdentifier::Simple {
                                                identifier: Identifier::Simple {
                                                    symbol: Symbol("i".to_string()),
                                                },
                                            }),
                                            Term::QualIdentifier(QualIdentifier::Simple {
                                                identifier: Identifier::Simple {
                                                    symbol: Symbol("v".to_string()),
                                                },
                                            }),
                                        ],
                                    },
                                    Term::QualIdentifier(QualIdentifier::Simple {
                                        identifier: Identifier::Simple {
                                            symbol: Symbol("j".to_string()),
                                        },
                                    }),
                                ],
                            },
                            Term::QualIdentifier(QualIdentifier::Simple {
                                identifier: Identifier::Simple {
                                    symbol: Symbol("v".to_string()),
                                },
                            }),
                        ],
                    },
                ],
            }),
        },
    }
}

fn generate_write_preserves_other_axiom(index_sort: &str, value_sort: &str) -> Command {
    let array_sort = string_to_sort(&format!("Array_{}_{}", index_sort, value_sort));
    let idx_sort = string_to_sort(index_sort);
    let val_sort = string_to_sort(value_sort);

    let read_fn = format!("Read_{}_{}", index_sort, value_sort);
    let write_fn = format!("Write_{}_{}", index_sort, value_sort);

    Command::Assert {
        term: Term::Forall {
            vars: vec![
                (Symbol("a".to_string()), array_sort.clone()),
                (Symbol("i".to_string()), idx_sort.clone()),
                (Symbol("j".to_string()), idx_sort.clone()),
                (Symbol("v".to_string()), val_sort.clone()),
            ],
            term: Box::new(Term::Application {
                qual_identifier: QualIdentifier::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("=>".to_string()),
                    },
                },
                arguments: vec![
                    Term::Application {
                        qual_identifier: QualIdentifier::Simple {
                            identifier: Identifier::Simple {
                                symbol: Symbol("not".to_string()),
                            },
                        },
                        arguments: vec![Term::Application {
                            qual_identifier: QualIdentifier::Simple {
                                identifier: Identifier::Simple {
                                    symbol: Symbol("=".to_string()),
                                },
                            },
                            arguments: vec![
                                Term::QualIdentifier(QualIdentifier::Simple {
                                    identifier: Identifier::Simple {
                                        symbol: Symbol("i".to_string()),
                                    },
                                }),
                                Term::QualIdentifier(QualIdentifier::Simple {
                                    identifier: Identifier::Simple {
                                        symbol: Symbol("j".to_string()),
                                    },
                                }),
                            ],
                        }],
                    },
                    Term::Application {
                        qual_identifier: QualIdentifier::Simple {
                            identifier: Identifier::Simple {
                                symbol: Symbol("=".to_string()),
                            },
                        },
                        arguments: vec![
                            Term::Application {
                                qual_identifier: QualIdentifier::Simple {
                                    identifier: Identifier::Simple {
                                        symbol: Symbol(read_fn.clone()),
                                    },
                                },
                                arguments: vec![
                                    Term::Application {
                                        qual_identifier: QualIdentifier::Simple {
                                            identifier: Identifier::Simple {
                                                symbol: Symbol(write_fn),
                                            },
                                        },
                                        arguments: vec![
                                            Term::QualIdentifier(QualIdentifier::Simple {
                                                identifier: Identifier::Simple {
                                                    symbol: Symbol("a".to_string()),
                                                },
                                            }),
                                            Term::QualIdentifier(QualIdentifier::Simple {
                                                identifier: Identifier::Simple {
                                                    symbol: Symbol("i".to_string()),
                                                },
                                            }),
                                            Term::QualIdentifier(QualIdentifier::Simple {
                                                identifier: Identifier::Simple {
                                                    symbol: Symbol("v".to_string()),
                                                },
                                            }),
                                        ],
                                    },
                                    Term::QualIdentifier(QualIdentifier::Simple {
                                        identifier: Identifier::Simple {
                                            symbol: Symbol("j".to_string()),
                                        },
                                    }),
                                ],
                            },
                            Term::Application {
                                qual_identifier: QualIdentifier::Simple {
                                    identifier: Identifier::Simple {
                                        symbol: Symbol(read_fn),
                                    },
                                },
                                arguments: vec![
                                    Term::QualIdentifier(QualIdentifier::Simple {
                                        identifier: Identifier::Simple {
                                            symbol: Symbol("a".to_string()),
                                        },
                                    }),
                                    Term::QualIdentifier(QualIdentifier::Simple {
                                        identifier: Identifier::Simple {
                                            symbol: Symbol("j".to_string()),
                                        },
                                    }),
                                ],
                            },
                        ],
                    },
                ],
            }),
        },
    }
}

fn generate_const_array_axiom(index_sort: &str, value_sort: &str) -> Command {
    let idx_sort = string_to_sort(index_sort);
    let val_sort = string_to_sort(value_sort);

    let read_fn = format!("Read_{}_{}", index_sort, value_sort);
    let const_arr_fn = format!("ConstArr_{}_{}", index_sort, value_sort);

    Command::Assert {
        term: Term::Forall {
            vars: vec![
                (Symbol("v".to_string()), val_sort.clone()),
                (Symbol("i".to_string()), idx_sort.clone()),
            ],
            term: Box::new(Term::Application {
                qual_identifier: QualIdentifier::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("=".to_string()),
                    },
                },
                arguments: vec![
                    Term::Application {
                        qual_identifier: QualIdentifier::Simple {
                            identifier: Identifier::Simple {
                                symbol: Symbol(read_fn),
                            },
                        },
                        arguments: vec![
                            Term::Application {
                                qual_identifier: QualIdentifier::Simple {
                                    identifier: Identifier::Simple {
                                        symbol: Symbol(const_arr_fn),
                                    },
                                },
                                arguments: vec![Term::QualIdentifier(QualIdentifier::Simple {
                                    identifier: Identifier::Simple {
                                        symbol: Symbol("v".to_string()),
                                    },
                                })],
                            },
                            Term::QualIdentifier(QualIdentifier::Simple {
                                identifier: Identifier::Simple {
                                    symbol: Symbol("i".to_string()),
                                },
                            }),
                        ],
                    },
                    Term::QualIdentifier(QualIdentifier::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol("v".to_string()),
                        },
                    }),
                ],
            }),
        },
    }
}

/// No theory support (for strategies that don't use any specific theory)
pub struct ConcreteArrayTheory;

impl TheorySupport for ConcreteArrayTheory {
    fn get_uninterpreted_functions(&self) -> Vec<FunctionDeclaration> {
        vec![]
    }

    fn get_logic_string(&self) -> String {
        "QF_AUFLIA".to_string()
    }

    fn abstract_model(&self, model: VMTModel) -> (VMTModel, Vec<(String, String)>) {
        (model, vec![])
    }

    fn requires_abstraction(&self) -> bool {
        false
    }

    fn get_axiom_formulas(&self) -> Vec<Command> {
        vec![]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_function_declaration_creation() {
        let func_decl =
            FunctionDeclaration::new("test_func", vec![int_sort(), bool_sort()], int_sort());

        assert_eq!(func_decl.name, "test_func");
        assert_eq!(func_decl.arg_sorts.len(), 2);

        let command = func_decl.to_command();
        match command {
            Command::DeclareFun {
                symbol,
                parameters,
                sort,
            } => {
                assert_eq!(symbol.0, "test_func");
                assert_eq!(parameters.len(), 2);
                // Check that it's an int sort
                if let Sort::Simple {
                    identifier: Identifier::Simple { symbol },
                } = sort
                {
                    assert_eq!(symbol.0, "Int");
                }
            }
            _ => panic!("Expected DeclareFun command"),
        }
    }

    #[test]
    fn test_array_theory_support() {
        let array_theory = ArrayTheorySupport::new(vec![("Int".into(), "Int".into())]);

        // Test function declarations
        let functions = array_theory.get_uninterpreted_functions();
        assert_eq!(functions.len(), 3);

        let function_names: Vec<&str> = functions.iter().map(|f| f.name.as_str()).collect();
        assert!(function_names.contains(&"Read_Int_Int"));
        assert!(function_names.contains(&"Write_Int_Int"));
        assert!(function_names.contains(&"ConstArr_Int_Int"));

        // Test logic string
        assert_eq!(array_theory.get_logic_string(), "UFLIA");

        // Test requires abstraction
        assert!(array_theory.requires_abstraction());
    }

    #[test]
    fn test_list_theory_support() {
        let list_theory = ListTheorySupport;

        // Test function declarations
        let functions = list_theory.get_uninterpreted_functions();
        assert_eq!(functions.len(), 10);

        let function_names: Vec<&str> = functions.iter().map(|f| f.name.as_str()).collect();
        assert!(function_names.contains(&"nil"));
        assert!(function_names.contains(&"cons"));
        assert!(function_names.contains(&"head"));
        assert!(function_names.contains(&"tail"));
        assert!(function_names.contains(&"length"));
        assert!(function_names.contains(&"append"));
        assert!(function_names.contains(&"reverse"));
        assert!(function_names.contains(&"nth"));
        assert!(function_names.contains(&"update-nth"));
        assert!(function_names.contains(&"is-nil"));

        // Test logic string
        assert_eq!(list_theory.get_logic_string(), "QF_LIA");

        // Test requires abstraction
        assert!(!list_theory.requires_abstraction());
    }

    #[test]
    fn test_no_theory_support() {
        let no_theory = ConcreteArrayTheory;

        // Test function declarations
        let functions = no_theory.get_uninterpreted_functions();
        assert_eq!(functions.len(), 0);

        // Test logic string
        assert_eq!(no_theory.get_logic_string(), "QF_AUFLIA");

        // Test requires abstraction
        assert!(!no_theory.requires_abstraction());
    }

    #[test]
    fn test_list_function_signatures() {
        let list_theory = ListTheorySupport;
        let functions = list_theory.get_uninterpreted_functions();

        // Find specific functions and test their signatures
        let cons_func = functions.iter().find(|f| f.name == "cons").unwrap();
        assert_eq!(cons_func.arg_sorts.len(), 2); // Int, ListInt

        let head_func = functions.iter().find(|f| f.name == "head").unwrap();
        assert_eq!(head_func.arg_sorts.len(), 1); // ListInt

        let append_func = functions.iter().find(|f| f.name == "append").unwrap();
        assert_eq!(append_func.arg_sorts.len(), 2); // ListInt, ListInt

        let nth_func = functions.iter().find(|f| f.name == "nth").unwrap();
        assert_eq!(nth_func.arg_sorts.len(), 2); // ListInt, Int

        let update_nth_func = functions.iter().find(|f| f.name == "update-nth").unwrap();
        assert_eq!(update_nth_func.arg_sorts.len(), 3); // ListInt, Int, Int
    }

    #[test]
    fn test_array_axioms_int_int() {
        let theory = ArrayWithQuantifiersTheorySupport::new(vec![("Int".into(), "Int".into())]);
        let axioms = theory.get_axiom_formulas();

        // Should generate 3 axioms for 1 type
        assert_eq!(axioms.len(), 3);

        // Verify each axiom is an Assert command with Forall
        for axiom in &axioms {
            match axiom {
                Command::Assert { term } => match term {
                    Term::Forall { .. } => {} // Good
                    _ => panic!("Expected Forall term in axiom"),
                },
                _ => panic!("Expected Assert command"),
            }
        }
    }

    #[test]
    fn test_array_axioms_bitvec() {
        let theory =
            ArrayWithQuantifiersTheorySupport::new(vec![("BitVec32".into(), "Int".into())]);
        let axioms = theory.get_axiom_formulas();

        // Should generate 3 axioms for BitVec32 -> Int arrays
        assert_eq!(axioms.len(), 3);

        let axiom_strings: Vec<String> = axioms.iter().map(|cmd| format!("{:?}", cmd)).collect();

        for axiom_str in &axiom_strings {
            assert!(
                axiom_str.contains("Read_BitVec32_Int"),
                "Axiom should contain Read_BitVec32_Int function"
            );
        }

        assert!(
            axiom_strings
                .iter()
                .any(|s| s.contains("Write_BitVec32_Int")),
            "At least one axiom should contain Write_BitVec32_Int"
        );

        assert!(
            axiom_strings
                .iter()
                .any(|s| s.contains("ConstArr_BitVec32_Int")),
            "At least one axiom should contain ConstArr_BitVec32_Int"
        );
    }

    #[test]
    fn test_array_axioms_nested_arrays() {
        let theory =
            ArrayWithQuantifiersTheorySupport::new(vec![("Int".into(), "Array_Int_Int".into())]);
        let axioms = theory.get_axiom_formulas();

        // Should generate 3 axioms for nested arrays
        assert_eq!(axioms.len(), 3);

        let axiom_strings: Vec<String> = axioms.iter().map(|cmd| format!("{:?}", cmd)).collect();

        for axiom_str in &axiom_strings {
            assert!(
                axiom_str.contains("Read_Int_Array_Int_Int"),
                "Axiom should contain Read_Int_Array_Int_Int function for nested arrays"
            );
        }

        assert!(
            axiom_strings
                .iter()
                .any(|s| s.contains("Write_Int_Array_Int_Int")),
            "Should have Write_Int_Array_Int_Int for nested arrays"
        );

        assert!(
            axiom_strings
                .iter()
                .any(|s| s.contains("ConstArr_Int_Array_Int_Int")),
            "Should have ConstArr_Int_Array_Int_Int for nested arrays"
        );

        // Verify the array sort type is correct
        assert!(
            axiom_strings
                .iter()
                .any(|s| s.contains("Array_Int_Array_Int_Int")),
            "Should reference Array_Int_Array_Int_Int sort"
        );
    }

    #[test]
    fn test_array_axioms_multiple_types() {
        let theory = ArrayWithQuantifiersTheorySupport::new(vec![
            ("Int".into(), "Int".into()),
            ("BitVec32".into(), "Int".into()),
            ("Int".into(), "Array_Int_Int".into()),
        ]);
        let axioms = theory.get_axiom_formulas();

        assert_eq!(axioms.len(), 9);

        let axiom_strings: Vec<String> = axioms.iter().map(|cmd| format!("{:?}", cmd)).collect();

        assert!(
            axiom_strings.iter().any(|s| s.contains("Read_Int_Int")),
            "Should have Int_Int axioms"
        );
        assert!(
            axiom_strings
                .iter()
                .any(|s| s.contains("Read_BitVec32_Int")),
            "Should have BitVec32_Int axioms"
        );
        assert!(
            axiom_strings
                .iter()
                .any(|s| s.contains("Read_Int_Array_Int_Int")),
            "Should have nested array axioms"
        );
    }

    #[test]
    fn test_string_to_sort_helper() {
        // Test the helper function creates correct sorts
        let int_sort = string_to_sort("Int");
        assert_eq!(
            format!("{:?}", int_sort),
            "Simple { identifier: Simple { symbol: Symbol(\"Int\") } }"
        );

        // BitVec32 is correctly parsed as an indexed sort (_ BitVec 32)
        let bitvec_sort = string_to_sort("BitVec32");
        assert_eq!(
            format!("{:?}", bitvec_sort),
            "Simple { identifier: Indexed { symbol: Symbol(\"BitVec\"), indices: [Numeral(32)] } }"
        );

        // Non-bitvector sorts remain as simple identifiers
        let nested_sort = string_to_sort("Array_Int_Int");
        assert_eq!(
            format!("{:?}", nested_sort),
            "Simple { identifier: Simple { symbol: Symbol(\"Array_Int_Int\") } }"
        );
    }
}
