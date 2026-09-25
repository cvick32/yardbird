//! VMT preparation: resolve requested ownership before changing the problem.
//! Parser analysis describes syntax; this module decides which abstractions to
//! apply and keeps the resulting model, refinement plans and solver vocabulary
//! together. A delegated theory is never abstracted and translated back later.
use std::{fmt, str::FromStr};

use smt2parser::{
    analysis::theories::TheoryFeatures,
    concrete::{Command, Term},
    vmt::VMTModel,
};

use super::{
    array::{encodings::EncodingOptions, refinement::ArrayRefinement},
    quantifiers::refinement::QuantifierRefinement,
};
use crate::{
    theory_support::{FunctionDeclaration, TheorySupport},
    Theory,
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum TheorySelection {
    #[default]
    Auto,
    Explicit(Vec<Theory>),
}

impl TheorySelection {
    pub fn includes(&self, theory: Theory) -> bool {
        match self {
            Self::Auto => matches!(theory, Theory::Array | Theory::Quantifiers),
            Self::Explicit(theories) => theories.contains(&theory),
        }
    }

    pub fn legacy_theory(&self) -> Option<Theory> {
        self.includes(Theory::List).then_some(Theory::List)
    }
}

impl FromStr for TheorySelection {
    type Err = String;
    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "auto" => return Ok(Self::Auto),
            "none" => return Ok(Self::Explicit(vec![])),
            _ => {}
        }
        let mut theories = Vec::new();
        for name in value.split(',') {
            let theory = match name.trim() {
                "array" => Theory::Array,
                "quantifiers" => Theory::Quantifiers,
                "list" => Theory::List,
                other => {
                    return Err(format!(
                        "unknown theory '{other}'; use auto, none, array, quantifiers, or list"
                    ))
                }
            };
            if !theories.contains(&theory) {
                theories.push(theory);
            }
        }
        if theories.len() > 1 && theories.contains(&Theory::List) {
            return Err("list cannot be combined with other theories yet".into());
        }
        theories.sort_by_key(|t| t.to_string());
        Ok(Self::Explicit(theories))
    }
}

impl fmt::Display for TheorySelection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Auto => f.write_str("auto"),
            Self::Explicit(theories) if theories.is_empty() => f.write_str("none"),
            Self::Explicit(theories) => f.write_str(
                &theories
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(","),
            ),
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Ownership {
    pub arrays: bool,
    pub quantifiers: bool,
}

pub(crate) struct PreparedVmt {
    pub model: VMTModel,
    pub array: ArrayRefinement,
    pub quantifier: QuantifierRefinement,
    pub theory: PreparedTheory,
    pub ownership: Ownership,
    pub notices: Vec<String>,
}

pub(crate) struct PreparationOptions<'a> {
    pub selection: &'a TheorySelection,
    pub preprocess_arrays: bool,
    pub encoding: EncodingOptions,
    pub property_cone: bool,
    pub profile: bool,
}

/// Ownership cannot make syntax usable by a backend that cannot translate it.
/// Check the source before abstraction can hide its sorts. This is deliberately
/// a check for known gaps, not a claim to validate every SMT operator.
pub(crate) fn validate_vmt_backend(
    model: &VMTModel,
    backend: crate::SolverBackend,
) -> anyhow::Result<()> {
    let features = TheoryFeatures::analyze(&model.as_commands());
    anyhow::ensure!(
        !features.parameterized_lists,
        "parameterized list VMT inputs are not supported"
    );
    anyhow::ensure!(
        backend != crate::SolverBackend::Z3 || !features.floating_point,
        "floating-point VMT inputs are not supported by the Z3 adapter"
    );
    Ok(())
}

pub(crate) fn prepare_vmt(
    model: VMTModel,
    options: PreparationOptions<'_>,
) -> anyhow::Result<PreparedVmt> {
    let features = TheoryFeatures::analyze(&model.as_commands());
    let automatic = matches!(options.selection, TheorySelection::Auto);
    let mut ownership = Ownership {
        arrays: (features.has_arrays() || features.lambdas > 0)
            && options.selection.includes(Theory::Array),
        quantifiers: (features.has_quantifiers() || features.lambdas > 0)
            && options.selection.includes(Theory::Quantifiers),
    };
    let mut notices = vec![];
    // Retain the existing all-abstract lambda path. Mixed lambda ownership is
    // intentionally outside this VMT change; use the encoded benchmark inputs.
    anyhow::ensure!(
        features.lambdas == 0
            || (ownership.arrays && ownership.quantifiers)
            || (!ownership.arrays && !ownership.quantifiers),
        "mixed theory ownership with lambdas is not supported; use a lambda-free encoded VMT input"
    );
    if let Some(reason) = ownership
        .arrays
        .then(|| array_abstraction_issue(&features, &model.as_commands()))
        .flatten()
    {
        anyhow::ensure!(
            automatic,
            "cannot abstract requested array theory: {reason}"
        );
        ownership.arrays = false;
        notices.push(format!("Delegating arrays to the solver: {reason}"));
    }
    if features.lambdas > 0 && !ownership.arrays && ownership.quantifiers {
        anyhow::ensure!(
            automatic,
            "quantifier-only ownership with lambdas is not supported"
        );
        ownership.quantifiers = false;
        notices.push("Delegating lambda binders with native arrays to the solver".into());
    }
    // Start each attempt from the source so provenance remains in source
    // vocabulary and a delegated pass leaves no partially lowered state behind.
    let (mut working, quantifier, array_types) = loop {
        let mut working = model.clone();
        let mut quantifier = QuantifierRefinement::default();
        if ownership.quantifiers {
            working = quantifier.configure_with_arrays(working, options.profile, ownership.arrays);
            if let Some(error) = &quantifier.configuration_error {
                anyhow::ensure!(automatic, "cannot abstract requested quantifiers: {error}");
                notices.push(format!(
                    "Delegating input quantifiers to the solver: {error}"
                ));
                working = model.clone();
                quantifier = QuantifierRefinement::default();
                ownership.quantifiers = false;
                if features.lambdas > 0 {
                    ownership.arrays = false;
                    notices.push(
                        "Delegating arrays with unsupported lambda binders to the solver".into(),
                    );
                }
            }
        }
        let mut types = vec![];
        if ownership.arrays && features.lambdas == 0 {
            match smt2parser::vmt::array_term_simplifier::ArrayTermSimplifier::abstract_commands(
                &working.as_commands(),
                options.preprocess_arrays,
            ) {
                Ok((commands, discovered)) => {
                    working = VMTModel::checked_from(commands)?;
                    types = discovered;
                }
                Err(error) => {
                    anyhow::ensure!(automatic, "cannot abstract requested array theory: {error}");
                    notices.push(format!("Delegating arrays to the solver: {error}"));
                    ownership.arrays = false;
                    // Binder formulas and signatures must be rebuilt natively too.
                    continue;
                }
            }
        }
        break (working, quantifier, types);
    };
    let mut array = ArrayRefinement::default();
    if ownership.arrays {
        let helpers = quantifier
            .plan
            .rules
            .iter()
            .map(|r| r.name.clone())
            .collect();
        working = if features.lambdas > 0 {
            array.configure_model(
                working,
                options.preprocess_arrays,
                options.encoding,
                options.property_cone,
                &helpers,
            )
        } else {
            array.configure_prepared(
                working,
                array_types,
                options.encoding,
                options.property_cone,
                &helpers,
            )
        };
    }
    if !ownership.arrays
        && (options.preprocess_arrays
            || options.encoding.recurrent_products
            || options.encoding.guarded_read_updates)
    {
        anyhow::bail!("array preprocessing and encoding options require Yardbird-owned arrays");
    }
    let theory = PreparedTheory::new(&working.as_commands(), &array.array_types, ownership.arrays);
    Ok(PreparedVmt {
        model: working,
        array,
        quantifier,
        theory,
        ownership,
        notices,
    })
}

fn array_abstraction_issue(features: &TheoryFeatures, commands: &[Command]) -> Option<String> {
    if features.sort_aliases || !features.array_extensions.is_empty() {
        return Some(
            "array abstraction does not yet support sort aliases or extended array operators"
                .into(),
        );
    }
    let names = smt2parser::vmt::array_abstractor::ArrayAbstractor::default();
    let reserved = features
        .array_sorts
        .iter()
        .flat_map(|(index, value)| {
            let suffix = format!(
                "{}_{}",
                names.sort_to_string(index),
                names.sort_to_string(value)
            );
            ["Array", "Read", "Write", "ConstArr"].map(|prefix| format!("{prefix}_{suffix}"))
        })
        .collect::<std::collections::HashSet<_>>();
    for command in commands {
        let symbol = match command {
            Command::DeclareFun { symbol, .. }
            | Command::DeclareConst { symbol, .. }
            | Command::DeclareSort { symbol, .. } => Some(symbol),
            Command::DefineFun { sig, .. } | Command::DefineFunRec { sig, .. } => Some(&sig.name),
            _ => None,
        };
        if let Some(symbol) = symbol.filter(|s| reserved.contains(&s.0)) {
            return Some(format!(
                "generated array symbol {symbol} conflicts with an input declaration"
            ));
        }
    }
    None
}

/// Solver declarations and logic describe the prepared problem, never a
/// representation that a solver adapter must undo.
#[derive(Clone)]
pub(crate) struct PreparedTheory {
    functions: Vec<FunctionDeclaration>,
    logic: String,
    abstract_arrays: bool,
}

impl PreparedTheory {
    fn new(commands: &[Command], array_types: &[(String, String)], abstract_arrays: bool) -> Self {
        let logic = Self::logic_for(commands, abstract_arrays);
        Self {
            functions: crate::theory_support::get_uninterpreted_array_functions(array_types),
            logic,
            abstract_arrays,
        }
    }
    fn logic_for(commands: &[Command], abstract_arrays: bool) -> String {
        let features = TheoryFeatures::analyze(commands);
        if features.reals
            || features.strings
            || features.floating_point
            || (features.integers && features.bitvectors)
        {
            "ALL".into()
        } else {
            format!(
                "{}{}UF{}",
                if abstract_arrays || features.has_quantifiers() || features.lambdas > 0 {
                    ""
                } else {
                    "QF_"
                },
                if features.has_arrays() { "A" } else { "" },
                if features.bitvectors {
                    "BV"
                } else if features.integers && features.nonlinear_arithmetic {
                    "NIA"
                } else if features.integers {
                    "LIA"
                } else {
                    ""
                }
            )
        }
    }
}

impl TheorySupport for PreparedTheory {
    fn get_uninterpreted_functions(&self) -> Vec<FunctionDeclaration> {
        self.functions.clone()
    }
    fn get_axiom_formulas(&self) -> Vec<Command> {
        vec![]
    }
    fn get_logic_string(&self) -> anyhow::Result<String> {
        Ok(self.logic.clone())
    }
    fn get_logic_string_for_problem(
        &self,
        terms: &[&Term],
        commands: &[Command],
    ) -> anyhow::Result<String> {
        let mut all = commands.to_vec();
        all.extend(terms.iter().map(|term| Command::Assert {
            term: (*term).clone(),
        }));
        Ok(Self::logic_for(&all, self.abstract_arrays))
    }

    fn abstract_model(&self, model: VMTModel) -> (VMTModel, Vec<(String, String)>) {
        (model, vec![])
    }
    fn requires_abstraction(&self) -> bool {
        self.abstract_arrays
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use smt2parser::{concrete::SyntaxBuilder, CommandStream};

    fn model(init: &str, declarations: &str) -> VMTModel {
        let input = format!(
            "{declarations}
            (define-fun init () Bool (! {init} :init true))
            (define-fun trans () Bool (! true :trans true))
            (define-fun prop () Bool (! true :invar-property 0))"
        );
        VMTModel::checked_from(
            CommandStream::new(input.as_bytes(), SyntaxBuilder, None)
                .collect::<Result<Vec<_>, _>>()
                .unwrap(),
        )
        .unwrap()
    }

    fn prepare(model: VMTModel, selection: &str) -> anyhow::Result<PreparedVmt> {
        prepare_vmt(
            model,
            PreparationOptions {
                selection: &selection.parse().unwrap(),
                preprocess_arrays: false,
                encoding: EncodingOptions::default(),
                property_cone: false,
                profile: false,
            },
        )
    }

    #[test]
    fn auto_delegates_failed_quantifier_lowering_atomically_with_a_notice() {
        let original = model(
            "(forall ((b Bool)) (match b ((true true) (false true))))",
            "",
        );
        let prepared = prepare(original.clone(), "auto").unwrap();
        assert!(!prepared.ownership.quantifiers);
        assert_eq!(prepared.model.as_commands(), original.as_commands());
        assert_eq!(prepared.notices.len(), 1);
        assert!(prepared.notices[0].contains("Delegating input quantifiers"));
        assert!(prepared.quantifier.plan.rules.is_empty());
        let error = prepare(original, "quantifiers").err().unwrap().to_string();
        assert!(
            error.contains("cannot abstract requested quantifiers"),
            "{error}"
        );
    }

    #[test]
    fn array_name_conflicts_delegate_without_abandoning_quantifiers() {
        let source = model(
            "(forall ((i Int)) (= (select a i) 0))",
            "(declare-fun a () (Array Int Int)) (declare-fun Read_Int_Int (Int) Bool)",
        );
        let prepared = prepare(source.clone(), "auto").unwrap();
        assert!(!prepared.ownership.arrays && prepared.ownership.quantifiers);
        assert_eq!(prepared.notices.len(), 1);
        assert!(prepared.notices[0].contains("conflicts with an input declaration"));
        assert!(prepared
            .quantifier
            .plan
            .rules
            .iter()
            .any(|r| r.body.to_string().contains("(select ")));
        assert!(prepare(source, "array").is_err());
    }

    #[test]
    fn ordinary_array_preparation_preserves_the_existing_encoding() {
        let source =
            VMTModel::from_path("examples/array/array_init_increm_two_arrs_const.vmt").unwrap();
        let mut quantifier = QuantifierRefinement::default();
        let previous = quantifier.configure_model(source.clone(), false);
        let (previous, _) = previous.abstract_array_theory();
        let prepared = prepare(source, "auto").unwrap();
        assert_eq!(previous.as_commands(), prepared.model.as_commands());
    }

    #[test]
    fn array_abstraction_preserves_backend_binders_and_their_array_sorts() {
        let original = model(
            "(forall ((a (Array node Bool)) (i node)) (= (select (store a i true) i) true))",
            "(declare-sort node 0)",
        );
        let prepared = prepare(original, "array").unwrap();
        let output = prepared.model.as_vmt_string();
        assert!(
            output.contains("(forall ((a Array_node_Bool) (i node))"),
            "{output}"
        );
        assert!(output.contains("Read_node_Bool"));
        assert!(!output.contains("Read_Int_Int"));
        assert!(!TheoryFeatures::analyze(&prepared.model.as_commands()).has_arrays());
        assert!(!prepared.ownership.quantifiers);
    }

    #[test]
    fn quantifier_only_preparation_preserves_array_valued_domains() {
        let original = model(
            "(forall ((a (Array Int Bool))) (= (select a 0) (select a 0)))",
            "",
        );
        let prepared = prepare(original, "quantifiers").unwrap();
        assert!(prepared.quantifier.plan.rules.iter().any(|r| r
            .variables
            .iter()
            .any(|(_, sort)| sort.to_string() == "(Array Int Bool)")));
        let output = prepared.model.as_vmt_string();
        assert!(!output.contains("Array_Int_Bool"));
        assert!(!output.contains("Read_"));
        assert!(prepared.theory.get_uninterpreted_functions().is_empty());
    }
}
