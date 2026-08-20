use std::vec;

use anyhow::{bail, Result};
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
    fn get_logic_string(&self) -> Result<String>;

    /// Returns a logic strong enough for the arithmetic used by these terms.
    fn get_logic_string_for_terms(&self, terms: &[&Term]) -> Result<String> {
        let logic = finalize_logic(self.get_logic_string()?, terms, &[]);
        validate_logic_for_terms(&logic, terms)?;
        Ok(logic)
    }

    /// Returns a logic strong enough for both the asserted terms and the
    /// declarations in a complete problem.
    fn get_logic_string_for_problem(
        &self,
        terms: &[&Term],
        commands: &[Command],
    ) -> Result<String> {
        let logic = finalize_logic(self.get_logic_string()?, terms, commands);
        validate_logic_for_terms(&logic, terms)?;
        validate_logic_for_commands(&logic, commands)?;
        Ok(logic)
    }

    /// Abstracts the VMT model for this theory (replaces theory-specific operations with uninterpreted functions)
    fn abstract_model(&self, model: VMTModel) -> (VMTModel, Vec<(String, String)>);

    /// Returns true if this theory requires abstraction
    fn requires_abstraction(&self) -> bool;

    /// Returns true when the theory is meaningful only for array-bearing inputs.
    fn requires_array_information(&self) -> bool {
        false
    }

    /// Returns true if this theory support uses quantified axioms
    /// (e.g., read-after-write axiom for arrays)
    fn uses_quantified_axioms(&self) -> bool {
        false // Default: no axioms
    }
}

fn validate_logic_for_terms(logic: &str, terms: &[&Term]) -> Result<()> {
    if logic == "ALL" {
        return Ok(());
    }

    let uses_bitvectors = terms.iter().any(|term| term_uses_bitvectors(term));
    if uses_bitvectors && !logic.contains("BV") {
        bail!("selected SMT logic {logic} does not support bit-vector terms");
    }

    let uses_native_arrays = terms.iter().any(|term| term_uses_native_arrays(term));
    if uses_native_arrays && !logic_supports_native_arrays(logic) {
        bail!("selected SMT logic {logic} does not support native array terms");
    }

    let uses_quantifiers = terms.iter().any(|term| term_uses_quantifiers(term));
    if uses_quantifiers && logic.starts_with("QF_") {
        bail!("selected SMT logic {logic} does not support quantified terms");
    }

    Ok(())
}

pub(crate) fn validate_logic_for_commands(logic: &str, commands: &[Command]) -> Result<()> {
    if logic == "ALL" {
        return Ok(());
    }

    let commands = commands.iter().map(ToString::to_string).collect::<Vec<_>>();
    let uses_bitvectors = commands.iter().any(|command| {
        command.contains("BitVec")
            || command.contains("#x")
            || command.contains("#b")
            || command.contains("(bv")
    });
    if uses_bitvectors && !logic.contains("BV") {
        bail!("selected SMT logic {logic} does not support bit-vector declarations or terms");
    }

    let uses_integers = commands
        .iter()
        .any(|command| command.contains(" Int") || command.contains("(to_int "));
    if uses_integers && !(logic.contains("IA") || logic.contains("IRA")) {
        bail!("selected SMT logic {logic} does not support integer declarations or terms");
    }

    let uses_reals = commands
        .iter()
        .any(|command| command.contains(" Real") || command.contains("(to_real "));
    if uses_reals && !logic.contains("RA") {
        bail!("selected SMT logic {logic} does not support real declarations or terms");
    }

    let uses_floating_point = commands
        .iter()
        .any(|command| command.contains("FloatingPoint") || command.contains("(_ fp "));
    if uses_floating_point && !logic.contains("FP") {
        bail!("selected SMT logic {logic} does not support floating-point declarations or terms");
    }

    let uses_native_arrays = commands.iter().any(|command| {
        command.contains("(Array ") || command.contains("(select ") || command.contains("(store ")
    });
    if uses_native_arrays && !logic_supports_native_arrays(logic) {
        bail!("selected SMT logic {logic} does not support native array declarations or terms");
    }

    let uses_quantifiers = commands.iter().any(|command| {
        command.contains("(lambda ") || command.contains("(forall ") || command.contains("(exists ")
    });
    if uses_quantifiers && logic.starts_with("QF_") {
        bail!("selected SMT logic {logic} does not support quantified terms");
    }

    Ok(())
}

fn logic_supports_native_arrays(logic: &str) -> bool {
    logic == "ALL" || logic.strip_prefix("QF_").unwrap_or(logic).starts_with('A')
}

fn logic_supports_integers(logic: &str) -> bool {
    logic == "ALL" || logic.contains("IA") || logic.contains("IRA")
}

fn logic_supports_bitvectors(logic: &str) -> bool {
    logic == "ALL" || logic.contains("BV")
}

fn widen_logic_for_integers(logic: &str) -> String {
    if logic_supports_integers(logic) {
        return logic.to_string();
    }
    if logic_supports_bitvectors(logic) {
        return "ALL".to_string();
    }

    match logic {
        "QF_UF" => "QF_UFLIA",
        "UF" => "UFLIA",
        "QF_AUF" => "QF_AUFLIA",
        "AUF" => "AUFLIA",
        _ => "ALL",
    }
    .to_string()
}

fn widen_logic_for_bitvectors(logic: &str) -> String {
    if logic_supports_bitvectors(logic) {
        return logic.to_string();
    }
    if logic_supports_integers(logic) {
        return "ALL".to_string();
    }

    match logic {
        "QF_UF" => "QF_UFBV",
        "UF" => "UFBV",
        "QF_AUF" => "QF_AUFBV",
        "AUF" => "AUFBV",
        _ => "ALL",
    }
    .to_string()
}

fn finalize_logic(base_logic: String, terms: &[&Term], commands: &[Command]) -> String {
    let command_strings = commands.iter().map(ToString::to_string).collect::<Vec<_>>();
    let uses_quantifiers = terms.iter().any(|term| term_uses_quantifiers(term))
        || command_strings.iter().any(|command| {
            command.contains("(lambda ")
                || command.contains("(forall ")
                || command.contains("(exists ")
        });
    let uses_bitvectors = terms.iter().any(|term| term_uses_bitvectors(term))
        || command_strings.iter().any(|command| {
            command.contains("BitVec")
                || command.contains("#x")
                || command.contains("#b")
                || command.contains("(bv")
        });
    let uses_integers = command_strings
        .iter()
        .any(|command| command.contains(" Int") || command.contains("(to_int "));
    let uses_reals = command_strings
        .iter()
        .any(|command| command.contains(" Real") || command.contains("(to_real "));
    let uses_floating_point = command_strings
        .iter()
        .any(|command| command.contains("FloatingPoint") || command.contains("(_ fp "));

    let mut logic = base_logic;
    if uses_integers {
        logic = widen_logic_for_integers(&logic);
    }
    if uses_bitvectors {
        logic = widen_logic_for_bitvectors(&logic);
    }
    if uses_reals || uses_floating_point {
        logic = "ALL".to_string();
    }
    if uses_quantifiers {
        logic = logic.strip_prefix("QF_").unwrap_or(&logic).to_string();
    }
    if terms
        .iter()
        .any(|term| requires_nonlinear_integer_logic(term))
    {
        logic = nonlinear_integer_logic(&logic).to_string();
    }

    logic
}

fn term_uses_bitvectors(term: &Term) -> bool {
    match term {
        Term::Constant(smt2parser::concrete::Constant::Hexadecimal(_))
        | Term::Constant(smt2parser::concrete::Constant::Binary(_)) => true,
        Term::Constant(_) => false,
        Term::QualIdentifier(identifier) => qualified_identifier_uses_bitvectors(identifier),
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let name = qual_identifier.get_name();
            name.starts_with("bv")
                || matches!(
                    name.as_str(),
                    "concat"
                        | "extract"
                        | "repeat"
                        | "zero_extend"
                        | "sign_extend"
                        | "rotate_left"
                        | "rotate_right"
                )
                || qualified_identifier_uses_bitvectors(qual_identifier)
                || arguments.iter().any(term_uses_bitvectors)
        }
        Term::Let { var_bindings, term } => {
            var_bindings
                .iter()
                .any(|(_, binding)| term_uses_bitvectors(binding))
                || term_uses_bitvectors(term)
        }
        Term::Lambda { vars, term } | Term::Forall { vars, term } | Term::Exists { vars, term } => {
            vars.iter().any(|(_, sort)| sort_uses_bitvectors(sort)) || term_uses_bitvectors(term)
        }
        Term::Match { term, cases } => {
            term_uses_bitvectors(term) || cases.iter().any(|(_, case)| term_uses_bitvectors(case))
        }
        Term::Attributes { term, .. } => term_uses_bitvectors(term),
    }
}

fn qualified_identifier_uses_bitvectors(identifier: &QualIdentifier) -> bool {
    match identifier {
        QualIdentifier::Simple { identifier } => identifier.to_string().contains("BitVec"),
        QualIdentifier::Sorted { identifier, sort } => {
            identifier.to_string().contains("BitVec") || sort_uses_bitvectors(sort)
        }
    }
}

fn sort_uses_bitvectors(sort: &Sort) -> bool {
    sort.to_string().contains("BitVec")
}

fn term_uses_native_arrays(term: &Term) -> bool {
    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            matches!(qual_identifier.get_name().as_str(), "select" | "store")
                || qualified_identifier_uses_native_arrays(qual_identifier)
                || arguments.iter().any(term_uses_native_arrays)
        }
        Term::QualIdentifier(identifier) => qualified_identifier_uses_native_arrays(identifier),
        Term::Let { var_bindings, term } => {
            var_bindings
                .iter()
                .any(|(_, binding)| term_uses_native_arrays(binding))
                || term_uses_native_arrays(term)
        }
        Term::Lambda { vars, term } | Term::Forall { vars, term } | Term::Exists { vars, term } => {
            vars.iter().any(|(_, sort)| sort_uses_native_arrays(sort))
                || term_uses_native_arrays(term)
        }
        Term::Match { term, cases } => {
            term_uses_native_arrays(term)
                || cases.iter().any(|(_, case)| term_uses_native_arrays(case))
        }
        Term::Attributes { term, .. } => term_uses_native_arrays(term),
        Term::Constant(_) => false,
    }
}

fn qualified_identifier_uses_native_arrays(identifier: &QualIdentifier) -> bool {
    matches!(identifier, QualIdentifier::Sorted { sort, .. } if sort_uses_native_arrays(sort))
}

fn sort_uses_native_arrays(sort: &Sort) -> bool {
    sort.to_string().contains("Array")
}

fn term_uses_quantifiers(term: &Term) -> bool {
    match term {
        Term::Lambda { .. } | Term::Forall { .. } | Term::Exists { .. } => true,
        Term::Application { arguments, .. } => arguments.iter().any(term_uses_quantifiers),
        Term::Let { var_bindings, term } => {
            var_bindings
                .iter()
                .any(|(_, binding)| term_uses_quantifiers(binding))
                || term_uses_quantifiers(term)
        }
        Term::Match { term, cases } => {
            term_uses_quantifiers(term) || cases.iter().any(|(_, case)| term_uses_quantifiers(case))
        }
        Term::Attributes { term, .. } => term_uses_quantifiers(term),
        Term::Constant(_) | Term::QualIdentifier(_) => false,
    }
}

fn nonlinear_integer_logic(logic: &str) -> &str {
    match logic {
        "LIA" => "NIA",
        "QF_LIA" => "QF_NIA",
        "UFLIA" => "UFNIA",
        "QF_UFLIA" => "QF_UFNIA",
        "AUFLIA" => "AUFNIA",
        "QF_AUFLIA" => "QF_AUFNIA",
        other => other,
    }
}

// Be conservative for replay: widening on these general operators preserves
// semantics without duplicating a full arithmetic-linearity analysis here.
fn requires_nonlinear_integer_logic(term: &Term) -> bool {
    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            matches!(qual_identifier.get_name().as_str(), "*" | "/" | "mod")
                || arguments.iter().any(requires_nonlinear_integer_logic)
        }
        Term::Let { var_bindings, term } => {
            var_bindings
                .iter()
                .any(|(_, binding)| requires_nonlinear_integer_logic(binding))
                || requires_nonlinear_integer_logic(term)
        }
        Term::Lambda { term, .. }
        | Term::Forall { term, .. }
        | Term::Exists { term, .. }
        | Term::Attributes { term, .. } => requires_nonlinear_integer_logic(term),
        Term::Match { term, cases } => {
            requires_nonlinear_integer_logic(term)
                || cases
                    .iter()
                    .any(|(_, case)| requires_nonlinear_integer_logic(case))
        }
        Term::Constant(_) | Term::QualIdentifier(_) => false,
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

    fn get_logic_string(&self) -> Result<String> {
        Ok("QF_LIA".to_string()) // Quantifier-free linear integer arithmetic + uninterpreted functions
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

fn has_integer_types(array_types: &[(String, String)]) -> bool {
    array_types
        .iter()
        .any(|(idx, val)| idx.contains("Int") || val.contains("Int"))
}

#[derive(Clone, Copy)]
enum ArrayEncoding {
    Abstracted,
    Native,
}

fn array_logic(
    array_types: &[(String, String)],
    quantifier_free: bool,
    encoding: ArrayEncoding,
) -> Result<String> {
    if array_types.is_empty() {
        bail!("array theory requires at least one discovered array type");
    }

    let has_bitvectors = has_bitvector_types(array_types);
    let has_integers = has_integer_types(array_types);
    if has_bitvectors && has_integers {
        return Ok("ALL".to_string());
    }

    let core_logic = match (encoding, has_bitvectors, has_integers) {
        (ArrayEncoding::Abstracted, true, false) => "UFBV",
        (ArrayEncoding::Abstracted, false, true) => "UFLIA",
        (ArrayEncoding::Abstracted, false, false) => "UF",
        (ArrayEncoding::Native, true, false) => "AUFBV",
        (ArrayEncoding::Native, false, true) => "AUFLIA",
        (ArrayEncoding::Native, false, false) => "AUF",
        (_, true, true) => unreachable!("mixed integer/bit-vector arrays use ALL"),
    };

    Ok(if quantifier_free {
        format!("QF_{core_logic}")
    } else {
        core_logic.to_string()
    })
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

    fn get_logic_string(&self) -> Result<String> {
        array_logic(&self.array_types, false, ArrayEncoding::Abstracted)
    }

    fn abstract_model(&self, model: VMTModel) -> (VMTModel, Vec<(String, String)>) {
        model.abstract_array_theory()
    }

    fn requires_abstraction(&self) -> bool {
        true
    }

    fn requires_array_information(&self) -> bool {
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

    fn get_logic_string(&self) -> Result<String> {
        array_logic(&self.array_types, false, ArrayEncoding::Abstracted)
    }

    fn abstract_model(&self, model: VMTModel) -> (VMTModel, Vec<(String, String)>) {
        model.abstract_array_theory()
    }

    fn requires_abstraction(&self) -> bool {
        true
    }

    fn requires_array_information(&self) -> bool {
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

/// Native Z3 array support.
pub struct ConcreteArrayTheory {
    pub array_types: Vec<(String, String)>,
}

impl ConcreteArrayTheory {
    pub fn new(array_types: Vec<(String, String)>) -> Self {
        Self { array_types }
    }
}

impl TheorySupport for ConcreteArrayTheory {
    fn get_uninterpreted_functions(&self) -> Vec<FunctionDeclaration> {
        vec![]
    }

    fn get_logic_string(&self) -> Result<String> {
        array_logic(&self.array_types, true, ArrayEncoding::Native)
    }

    fn abstract_model(&self, model: VMTModel) -> (VMTModel, Vec<(String, String)>) {
        (model, vec![])
    }

    fn requires_abstraction(&self) -> bool {
        false
    }

    fn requires_array_information(&self) -> bool {
        true
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
        assert_eq!(array_theory.get_logic_string().unwrap(), "UFLIA");

        // Test requires abstraction
        assert!(array_theory.requires_abstraction());
    }

    #[test]
    fn array_theory_rejects_models_without_array_types() {
        let array_theory = ArrayTheorySupport::new(vec![]);

        assert!(array_theory.get_logic_string().is_err());
    }

    #[test]
    fn array_theory_widens_for_additional_term_theories() {
        let array_theory = ArrayTheorySupport::new(vec![("Int".into(), "Int".into())]);
        let bitvector_term: Term = "(bvslt #x01 #x02)".parse().unwrap();

        assert_eq!(
            array_theory
                .get_logic_string_for_terms(&[&bitvector_term])
                .unwrap(),
            "ALL"
        );
    }

    #[test]
    fn logic_validation_checks_declared_sorts() {
        let command =
            smt2parser::get_command_from_command_string(b"(declare-fun x () (_ BitVec 8))");

        let error = validate_logic_for_commands("UFLIA", &[command]).unwrap_err();

        assert!(error.to_string().contains("bit-vector declarations"));
    }

    #[test]
    fn logic_validation_does_not_treat_lia_as_array_support() {
        let command =
            smt2parser::get_command_from_command_string(b"(declare-fun a () (Array client Bool))");

        let error = validate_logic_for_commands("UFLIA", &[command]).unwrap_err();

        assert!(error.to_string().contains("native array declarations"));
    }

    #[test]
    fn abstract_array_logic_uses_only_the_remaining_scalar_theories() {
        let pure_uf = ArrayTheorySupport::new(vec![("client".into(), "Bool".into())]);
        let integers = ArrayTheorySupport::new(vec![("Int".into(), "Bool".into())]);
        let bitvectors = ArrayTheorySupport::new(vec![("BitVec32".into(), "Bool".into())]);

        assert_eq!(pure_uf.get_logic_string().unwrap(), "UF");
        assert_eq!(integers.get_logic_string().unwrap(), "UFLIA");
        assert_eq!(bitvectors.get_logic_string().unwrap(), "UFBV");
    }

    #[test]
    fn quantified_abstract_array_logic_uses_uf_without_native_arrays() {
        let theory = ArrayWithQuantifiersTheorySupport::new(vec![("client".into(), "Bool".into())]);

        assert_eq!(theory.get_logic_string().unwrap(), "UF");
    }

    #[test]
    fn problem_logic_widens_for_scalar_declarations_without_restoring_arrays() {
        let abstract_theory = ArrayTheorySupport::new(vec![("client".into(), "Bool".into())]);
        let concrete_theory = ConcreteArrayTheory::new(vec![("client".into(), "Bool".into())]);
        let command = smt2parser::get_command_from_command_string(b"(declare-fun count () Int)");

        assert_eq!(
            abstract_theory
                .get_logic_string_for_problem(&[], std::slice::from_ref(&command))
                .unwrap(),
            "UFLIA"
        );
        assert_eq!(
            concrete_theory
                .get_logic_string_for_problem(&[], &[command])
                .unwrap(),
            "QF_AUFLIA"
        );
    }

    #[test]
    fn mixed_integer_and_bitvector_arrays_use_z3s_general_logic() {
        let theory = ConcreteArrayTheory::new(vec![("BitVec32".into(), "Int".into())]);

        assert_eq!(theory.get_logic_string().unwrap(), "ALL");
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
        assert_eq!(list_theory.get_logic_string().unwrap(), "QF_LIA");

        // Test requires abstraction
        assert!(!list_theory.requires_abstraction());
    }

    #[test]
    fn test_no_theory_support() {
        let no_theory = ConcreteArrayTheory::new(vec![("Int".into(), "Int".into())]);

        // Test function declarations
        let functions = no_theory.get_uninterpreted_functions();
        assert_eq!(functions.len(), 0);

        // Test logic string
        assert_eq!(no_theory.get_logic_string().unwrap(), "QF_AUFLIA");

        // Test requires abstraction
        assert!(!no_theory.requires_abstraction());
    }

    #[test]
    fn concrete_array_logic_widens_for_quantified_terms() {
        let theory = ConcreteArrayTheory::new(vec![
            ("client".into(), "Bool".into()),
            ("server".into(), "Bool".into()),
        ]);
        let term: Term = "(forall ((x client)) true)".parse().unwrap();

        assert_eq!(theory.get_logic_string_for_terms(&[&term]).unwrap(), "AUF");
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
