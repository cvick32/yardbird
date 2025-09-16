use smt2parser::concrete::{Command, Identifier, Sort, Symbol};
use smt2parser::vmt::VMTModel;

/// Trait for providing theory-specific function declarations and model abstractions
pub trait TheorySupport {
    /// Returns the list of uninterpreted functions that need to be declared in Z3
    fn get_uninterpreted_functions(&self) -> Vec<FunctionDeclaration>;

    /// Returns the SMT logic string for this theory (e.g., "QF_LIA", "UFLIA")
    fn get_logic_string(&self) -> String;

    /// Abstracts the VMT model for this theory (replaces theory-specific operations with uninterpreted functions)
    fn abstract_model(&self, model: VMTModel) -> VMTModel;

    /// Returns true if this theory requires abstraction
    fn requires_abstraction(&self) -> bool;
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

    fn abstract_model(&self, model: VMTModel) -> VMTModel {
        // For now, we don't need to abstract the model for lists since we're declaring them as uninterpreted
        // In the future, we could implement a ListAbstractor similar to ArrayAbstractor
        model
    }

    fn requires_abstraction(&self) -> bool {
        false // We declare functions directly rather than abstracting
    }
}

pub fn array_sort(index_sort: &str, element_sort: &str) -> Sort {
    Sort::Simple {
        identifier: Identifier::Simple {
            symbol: Symbol(format!("Array-{}-{}", index_sort, element_sort)),
        },
    }
}

/// Theory support for array operations (existing behavior)
pub struct ArrayTheorySupport;

impl TheorySupport for ArrayTheorySupport {
    fn get_uninterpreted_functions(&self) -> Vec<FunctionDeclaration> {
        let array_int_int_sort = array_sort("Int", "Int");
        let int_sort = int_sort();

        vec![
            // Array operations that get abstracted to uninterpreted functions
            FunctionDeclaration::new(
                "Read-Int-Int",
                vec![array_int_int_sort.clone(), int_sort.clone()],
                int_sort.clone(),
            ),
            FunctionDeclaration::new(
                "Write-Int-Int",
                vec![
                    array_int_int_sort.clone(),
                    int_sort.clone(),
                    int_sort.clone(),
                ],
                array_int_int_sort.clone(),
            ),
            FunctionDeclaration::new(
                "ConstArr-Int-Int",
                vec![int_sort.clone()],
                array_int_int_sort.clone(),
            ),
        ]
    }

    fn get_logic_string(&self) -> String {
        "UFLIA".to_string()
    }

    fn abstract_model(&self, model: VMTModel) -> VMTModel {
        model.abstract_array_theory()
    }

    fn requires_abstraction(&self) -> bool {
        true
    }
}

/// No theory support (for strategies that don't use any specific theory)
pub struct NoTheorySupport;

impl TheorySupport for NoTheorySupport {
    fn get_uninterpreted_functions(&self) -> Vec<FunctionDeclaration> {
        vec![]
    }

    fn get_logic_string(&self) -> String {
        "QF_LIA".to_string()
    }

    fn abstract_model(&self, model: VMTModel) -> VMTModel {
        model
    }

    fn requires_abstraction(&self) -> bool {
        false
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
        let array_theory = ArrayTheorySupport;

        // Test function declarations
        let functions = array_theory.get_uninterpreted_functions();
        assert_eq!(functions.len(), 3);

        let function_names: Vec<&str> = functions.iter().map(|f| f.name.as_str()).collect();
        assert!(function_names.contains(&"Read-Int-Int"));
        assert!(function_names.contains(&"Write-Int-Int"));
        assert!(function_names.contains(&"ConstArr-Int-Int"));

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
        let no_theory = NoTheorySupport;

        // Test function declarations
        let functions = no_theory.get_uninterpreted_functions();
        assert_eq!(functions.len(), 0);

        // Test logic string
        assert_eq!(no_theory.get_logic_string(), "QF_LIA");

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
}
