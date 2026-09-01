use smt2parser::{
    concrete::{QualIdentifier, Symbol, Term},
    vmt::split_framed_symbol,
};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt::Debug,
    rc::Rc,
};

/// One raw sequence interpolant returned by SMTInterpol.
///
/// Interpolants intentionally stay in the parser's syntax tree. Predicate
/// mining can inspect that tree directly without first normalizing the whole
/// formula through an e-graph.
#[derive(Clone, Eq, PartialEq)]
pub struct Interpolant {
    pub term: Term,
    pub interpolant_number: usize,
}

impl Interpolant {
    pub fn new(term: Term, interpolant_number: usize) -> Self {
        Self {
            term,
            interpolant_number,
        }
    }

    pub fn predicates(&self) -> PredicateCatalog {
        PredicateCatalog::from_interpolants(std::slice::from_ref(self))
    }
}

impl Debug for Interpolant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.interpolant_number, self.term)
    }
}

/// A serialized SMTInterpol sequence query and the BMC frame associated with
/// each interpolant boundary expected in the response.
#[derive(Clone, Debug)]
pub(crate) struct SequenceInterpolationQuery {
    pub smt2: String,
    pub depth: u16,
    pub logic: String,
    pub interpolant_frames: Vec<u16>,
}

/// One sequence interpolant at the boundary immediately after `frame`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SequenceInterpolantPartition {
    pub frame: u16,
    pub interpolant: Interpolant,
}

/// Frame-aware sequence interpolants and their structurally mined predicates.
#[derive(Clone, Debug)]
pub struct SequenceInterpolants {
    pub depth: u16,
    pub logic: String,
    pub partitions: Vec<SequenceInterpolantPartition>,
    pub predicates: PredicateCatalog,
}

impl SequenceInterpolants {
    pub fn new(depth: u16, logic: String, partitions: Vec<SequenceInterpolantPartition>) -> Self {
        let interpolants = partitions
            .iter()
            .map(|partition| partition.interpolant.clone())
            .collect::<Vec<_>>();
        let predicates = PredicateCatalog::from_interpolants(&interpolants);
        Self {
            depth,
            logic,
            partitions,
            predicates,
        }
    }
}

/// A state-variable occurrence found in a predicate.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PredicateVariable {
    /// The original VMT variable name without a BMC frame suffix.
    pub name: String,
    /// The absolute BMC frame, when the source symbol was framed.
    pub frame: Option<i64>,
}

impl PredicateVariable {
    fn from_symbol(symbol: &str) -> Self {
        match split_framed_symbol(symbol) {
            Some((name, frame)) => Self {
                name: unquote_symbol(&name).to_string(),
                frame: Some(frame),
            },
            None => Self {
                name: unquote_symbol(symbol).to_string(),
                frame: None,
            },
        }
    }
}

/// One structurally unique atomic predicate mined from the interpolant set.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PredicateCandidate {
    /// A standalone term. Any `let` aliases needed by this predicate have been
    /// resolved, but the surrounding interpolant has not been expanded.
    pub term: Term,
    /// Interpolants containing this exact predicate, in deterministic order.
    pub interpolant_numbers: BTreeSet<usize>,
    /// Free variable occurrences mentioned by the predicate.
    pub variables: BTreeSet<PredicateVariable>,
}

/// Structurally deduplicated predicates with an inverted state-variable index.
#[derive(Clone, Debug, Default)]
pub struct PredicateCatalog {
    candidates: Vec<PredicateCandidate>,
    by_variable: BTreeMap<String, Vec<usize>>,
}

impl PredicateCatalog {
    pub fn from_interpolants(interpolants: &[Interpolant]) -> Self {
        let mut catalog = Self::default();
        let mut candidate_by_term = HashMap::<Term, usize>::new();

        for interpolant in interpolants {
            PredicateCollector {
                interpolant_number: interpolant.interpolant_number,
                catalog: &mut catalog,
                candidate_by_term: &mut candidate_by_term,
            }
            .collect(&interpolant.term);
        }

        catalog
    }

    pub fn candidates(&self) -> &[PredicateCandidate] {
        &self.candidates
    }

    /// Return candidates mentioning `variable`, ignoring any supplied frame.
    pub fn candidates_for_variable<'a>(
        &'a self,
        variable: &str,
    ) -> impl Iterator<Item = &'a PredicateCandidate> + 'a {
        let variable = PredicateVariable::from_symbol(variable);
        self.by_variable
            .get(&variable.name)
            .into_iter()
            .flatten()
            .map(|index| &self.candidates[*index])
    }

    /// Return candidates mentioning one exact framed occurrence of `variable`.
    pub fn candidates_for_variable_at<'a>(
        &'a self,
        variable: &str,
        frame: i64,
    ) -> impl Iterator<Item = &'a PredicateCandidate> + 'a {
        let variable = PredicateVariable::from_symbol(variable);
        let target = PredicateVariable {
            name: variable.name.clone(),
            frame: Some(frame),
        };
        self.by_variable
            .get(&variable.name)
            .into_iter()
            .flatten()
            .map(|index| &self.candidates[*index])
            .filter(move |candidate| candidate.variables.contains(&target))
    }

    fn insert(&mut self, term: Term, interpolant_number: usize, index: &mut HashMap<Term, usize>) {
        if is_boolean_constant(&term) {
            return;
        }

        let variables = free_variables(&term);
        if variables.is_empty() || is_reflexive_relation(&term) {
            return;
        }

        let normalized_key = normalized_predicate_key(&term);
        if let Some(candidate_index) = index.get(&normalized_key).copied() {
            self.candidates[candidate_index]
                .interpolant_numbers
                .insert(interpolant_number);
            return;
        }

        let candidate_index = self.candidates.len();
        let base_variables = variables
            .iter()
            .map(|variable| variable.name.clone())
            .collect::<BTreeSet<_>>();
        self.candidates.push(PredicateCandidate {
            term: term.clone(),
            interpolant_numbers: BTreeSet::from([interpolant_number]),
            variables,
        });
        index.insert(normalized_key, candidate_index);
        for variable in base_variables {
            self.by_variable
                .entry(variable)
                .or_default()
                .push(candidate_index);
        }
    }
}

struct PredicateCollector<'a> {
    interpolant_number: usize,
    catalog: &'a mut PredicateCatalog,
    candidate_by_term: &'a mut HashMap<Term, usize>,
}

impl PredicateCollector<'_> {
    fn collect(&mut self, term: &Term) {
        self.collect_boolean(term, &BindingEnvironment::default());
    }

    fn collect_boolean(&mut self, term: &Term, bindings: &BindingEnvironment) {
        match term {
            Term::Attributes { term, .. } => self.collect_boolean(term, bindings),
            Term::Let { var_bindings, term } => {
                let nested = bindings.with_bindings(var_bindings);
                self.collect_boolean(term, &nested);
            }
            Term::QualIdentifier(identifier) => {
                let name = identifier.get_name();
                if let Some(BindingValue::Term(bound)) = bindings.lookup(&name) {
                    self.collect_boolean(&bound.term, &bound.environment);
                } else if name != "true" && name != "false" {
                    self.record(term, bindings);
                }
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => match qual_identifier.get_name().as_str() {
                "and" | "or" | "xor" | "=>" => {
                    for argument in arguments {
                        self.collect_boolean(argument, bindings);
                    }
                }
                "not" if arguments.len() == 1 => self.collect_boolean(&arguments[0], bindings),
                "ite" if arguments.len() == 3 => {
                    for argument in arguments {
                        self.collect_boolean(argument, bindings);
                    }
                }
                _ => self.record(term, bindings),
            },
            // Quantified atoms are not installable as ground auxiliary guards.
            Term::Forall { .. } | Term::Exists { .. } | Term::Lambda { .. } => {}
            // A match case is meaningful only under its pattern and scrutinee;
            // mining the case body alone could leak pattern-bound symbols into
            // a supposedly standalone candidate.
            Term::Match { .. } => {}
            Term::Constant(_) => {}
        }
    }

    fn record(&mut self, term: &Term, bindings: &BindingEnvironment) {
        let term = resolve_bindings(term, bindings);
        self.catalog
            .insert(term, self.interpolant_number, self.candidate_by_term);
    }
}

#[derive(Clone, Default)]
struct BindingEnvironment(Option<Rc<BindingFrame>>);

struct BindingFrame {
    values: HashMap<String, BindingValue>,
    parent: BindingEnvironment,
}

#[derive(Clone)]
enum BindingValue {
    Term(BoundTerm),
    Shadowed,
}

#[derive(Clone)]
struct BoundTerm {
    term: Term,
    environment: BindingEnvironment,
}

impl BindingEnvironment {
    fn with_bindings(&self, bindings: &[(Symbol, Term)]) -> Self {
        let values = bindings
            .iter()
            .map(|(symbol, term)| {
                (
                    symbol.0.clone(),
                    BindingValue::Term(BoundTerm {
                        term: term.clone(),
                        // SMT-LIB let bindings are simultaneous: sibling
                        // right-hand sides see only the incoming environment.
                        environment: self.clone(),
                    }),
                )
            })
            .collect();
        Self(Some(Rc::new(BindingFrame {
            values,
            parent: self.clone(),
        })))
    }

    fn with_shadowed(&self, symbols: &[Symbol]) -> Self {
        let values = symbols
            .iter()
            .map(|symbol| (symbol.0.clone(), BindingValue::Shadowed))
            .collect();
        Self(Some(Rc::new(BindingFrame {
            values,
            parent: self.clone(),
        })))
    }

    fn lookup(&self, name: &str) -> Option<BindingValue> {
        let mut frame = self.0.clone();
        while let Some(current) = frame {
            if let Some(value) = current.values.get(name) {
                return Some(value.clone());
            }
            frame = current.parent.0.clone();
        }
        None
    }
}

fn resolve_bindings(term: &Term, bindings: &BindingEnvironment) -> Term {
    match term {
        Term::Constant(_) => term.clone(),
        Term::QualIdentifier(identifier) => {
            resolve_identifier(identifier, bindings).unwrap_or_else(|| term.clone())
        }
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            if arguments.is_empty() {
                if let Some(resolved) = resolve_identifier(qual_identifier, bindings) {
                    return resolved;
                }
            }
            Term::Application {
                qual_identifier: qual_identifier.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| resolve_bindings(argument, bindings))
                    .collect(),
            }
        }
        Term::Let { var_bindings, term } => {
            let nested = bindings.with_bindings(var_bindings);
            resolve_bindings(term, &nested)
        }
        Term::Lambda { vars, term } => {
            let symbols = vars
                .iter()
                .map(|(symbol, _)| symbol.clone())
                .collect::<Vec<_>>();
            let nested = bindings.with_shadowed(&symbols);
            Term::Lambda {
                vars: vars.clone(),
                term: Box::new(resolve_bindings(term, &nested)),
            }
        }
        Term::Forall { vars, term } => {
            let symbols = vars
                .iter()
                .map(|(symbol, _)| symbol.clone())
                .collect::<Vec<_>>();
            let nested = bindings.with_shadowed(&symbols);
            Term::Forall {
                vars: vars.clone(),
                term: Box::new(resolve_bindings(term, &nested)),
            }
        }
        Term::Exists { vars, term } => {
            let symbols = vars
                .iter()
                .map(|(symbol, _)| symbol.clone())
                .collect::<Vec<_>>();
            let nested = bindings.with_shadowed(&symbols);
            Term::Exists {
                vars: vars.clone(),
                term: Box::new(resolve_bindings(term, &nested)),
            }
        }
        Term::Match { term, cases } => Term::Match {
            term: Box::new(resolve_bindings(term, bindings)),
            cases: cases
                .iter()
                .map(|(symbols, case)| {
                    let nested = bindings.with_shadowed(symbols);
                    (symbols.clone(), resolve_bindings(case, &nested))
                })
                .collect(),
        },
        // Attributes describe the source formula; the candidate itself should
        // be directly evaluable and installable.
        Term::Attributes { term, .. } => resolve_bindings(term, bindings),
    }
}

fn resolve_identifier(identifier: &QualIdentifier, bindings: &BindingEnvironment) -> Option<Term> {
    match bindings.lookup(&identifier.get_name()) {
        Some(BindingValue::Term(bound)) => Some(resolve_bindings(&bound.term, &bound.environment)),
        Some(BindingValue::Shadowed) | None => None,
    }
}

fn free_variables(term: &Term) -> BTreeSet<PredicateVariable> {
    let mut variables = BTreeSet::new();
    collect_free_variables(term, &mut BTreeSet::new(), &mut variables);
    variables
}

fn collect_free_variables(
    term: &Term,
    bound: &mut BTreeSet<String>,
    variables: &mut BTreeSet<PredicateVariable>,
) {
    match term {
        Term::Constant(_) => {}
        Term::QualIdentifier(identifier) => {
            collect_free_identifier(identifier, bound, variables);
        }
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            if arguments.is_empty() {
                collect_free_identifier(qual_identifier, bound, variables);
            }
            for argument in arguments {
                collect_free_variables(argument, bound, variables);
            }
        }
        Term::Let { var_bindings, term } => {
            for (_, value) in var_bindings {
                collect_free_variables(value, bound, variables);
            }
            with_bound_symbols(
                bound,
                var_bindings.iter().map(|(symbol, _)| symbol),
                |bound| collect_free_variables(term, bound, variables),
            );
        }
        Term::Lambda { vars, term } | Term::Forall { vars, term } | Term::Exists { vars, term } => {
            with_bound_symbols(bound, vars.iter().map(|(symbol, _)| symbol), |bound| {
                collect_free_variables(term, bound, variables)
            });
        }
        Term::Match { term, cases } => {
            collect_free_variables(term, bound, variables);
            for (symbols, case) in cases {
                with_bound_symbols(bound, symbols.iter(), |bound| {
                    collect_free_variables(case, bound, variables)
                });
            }
        }
        Term::Attributes { term, .. } => collect_free_variables(term, bound, variables),
    }
}

fn collect_free_identifier(
    identifier: &QualIdentifier,
    bound: &BTreeSet<String>,
    variables: &mut BTreeSet<PredicateVariable>,
) {
    let name = identifier.get_name();
    if name != "true" && name != "false" && !bound.contains(&name) {
        variables.insert(PredicateVariable::from_symbol(&name));
    }
}

fn with_bound_symbols<'a>(
    bound: &mut BTreeSet<String>,
    symbols: impl Iterator<Item = &'a Symbol>,
    visit: impl FnOnce(&mut BTreeSet<String>),
) {
    let newly_bound = symbols
        .filter_map(|symbol| bound.insert(symbol.0.clone()).then_some(symbol.0.clone()))
        .collect::<Vec<_>>();
    visit(bound);
    for symbol in newly_bound {
        bound.remove(&symbol);
    }
}

fn is_boolean_constant(term: &Term) -> bool {
    matches!(
        term,
        Term::QualIdentifier(identifier) if matches!(identifier.get_name().as_str(), "true" | "false")
    )
}

fn is_reflexive_relation(term: &Term) -> bool {
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        return false;
    };
    matches!(
        qual_identifier.get_name().as_str(),
        "=" | "distinct" | "<" | "<=" | ">" | ">="
    ) && arguments.len() >= 2
        && arguments.windows(2).all(|pair| pair[0] == pair[1])
}

/// Build a semantics-preserving key for candidate deduplication while keeping
/// the first predicate's original spelling in the catalog.
fn normalized_predicate_key(term: &Term) -> Term {
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        return term.clone();
    };

    let mut arguments = arguments
        .iter()
        .map(normalized_predicate_key)
        .collect::<Vec<_>>();
    let name = qual_identifier.get_name();
    let qual_identifier = match (name.as_str(), arguments.as_mut_slice()) {
        (">", [left, right]) => {
            std::mem::swap(left, right);
            QualIdentifier::simple("<")
        }
        (">=", [left, right]) => {
            std::mem::swap(left, right);
            QualIdentifier::simple("<=")
        }
        _ => qual_identifier.clone(),
    };

    if matches!(
        qual_identifier.get_name().as_str(),
        "=" | "distinct"
            | "+"
            | "*"
            | "and"
            | "or"
            | "xor"
            | "bvadd"
            | "bvmul"
            | "bvand"
            | "bvor"
            | "bvxor"
    ) {
        arguments.sort_by_cached_key(ToString::to_string);
    }

    Term::Application {
        qual_identifier,
        arguments,
    }
}

fn unquote_symbol(symbol: &str) -> &str {
    symbol
        .strip_prefix('|')
        .and_then(|symbol| symbol.strip_suffix('|'))
        .unwrap_or(symbol)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn interpolant(number: usize, term: &str) -> Interpolant {
        Interpolant::new(term.parse().unwrap(), number)
    }

    fn candidate_terms(catalog: &PredicateCatalog) -> Vec<String> {
        catalog
            .candidates()
            .iter()
            .map(|candidate| candidate.term.to_string())
            .collect()
    }

    #[test]
    fn extracts_and_deduplicates_atomic_predicates() {
        let interpolants = [
            interpolant(
                0,
                "(and (<= i@0 0) (or (= (Read_Int_Int a@0 i@0) value@0) (<= i@0 0)) true)",
            ),
            interpolant(1, "(=> (> limit@1 i@1) (<= i@0 0))"),
        ];

        let catalog = PredicateCatalog::from_interpolants(&interpolants);

        assert_eq!(
            candidate_terms(&catalog),
            [
                "(<= i@0 0)",
                "(= (Read_Int_Int a@0 i@0) value@0)",
                "(> limit@1 i@1)",
            ]
        );
        assert_eq!(
            catalog.candidates()[0].interpolant_numbers,
            BTreeSet::from([0, 1])
        );
    }

    #[test]
    fn resolves_only_let_bindings_needed_by_each_predicate() {
        let interpolant = interpolant(
            0,
            "(let ((delta (* (- 1) limit@2))) (let ((guard (<= (+ i@2 delta) 0)) (next-value (+ i@2 1))) (and guard (= next-value j@3))))",
        );

        assert!(matches!(interpolant.term, Term::Let { .. }));
        assert_eq!(
            candidate_terms(&interpolant.predicates()),
            ["(<= (+ i@2 (* (- 1) limit@2)) 0)", "(= (+ i@2 1) j@3)"]
        );
    }

    #[test]
    fn indexes_candidates_by_base_and_framed_variable() {
        let catalog = interpolant(
            0,
            "(and (< i@1 n@1) (= i@2 (+ i@1 1)) (= |state.value@2| 7))",
        )
        .predicates();

        let for_i = catalog
            .candidates_for_variable("i")
            .map(|candidate| candidate.term.to_string())
            .collect::<Vec<_>>();
        assert_eq!(for_i, ["(< i@1 n@1)", "(= i@2 (+ i@1 1))"]);

        let for_i_at_2 = catalog
            .candidates_for_variable_at("i@99", 2)
            .map(|candidate| candidate.term.to_string())
            .collect::<Vec<_>>();
        assert_eq!(for_i_at_2, ["(= i@2 (+ i@1 1))"]);

        let quoted = catalog
            .candidates_for_variable("|state.value|")
            .map(|candidate| candidate.term.to_string())
            .collect::<Vec<_>>();
        assert_eq!(quoted, ["(= state.value@2 7)"]);
    }

    #[test]
    fn strips_attributes_and_ignores_quantified_predicates() {
        let catalog = interpolant(
            0,
            "(and (! (< x@0 4) :predicate true) (forall ((i Int)) (< i x@0)))",
        )
        .predicates();

        assert_eq!(candidate_terms(&catalog), ["(< x@0 4)"]);
    }

    #[test]
    fn filters_ground_and_reflexive_predicates() {
        let catalog = interpolant(
            0,
            "(and (= 1 1) (< 0 0) (= i@0 i@0) (<= (+ i@0 1) (+ i@0 1)) (< i@0 n@0))",
        )
        .predicates();

        assert_eq!(candidate_terms(&catalog), ["(< i@0 n@0)"]);
    }

    #[test]
    fn deduplicates_symmetric_and_reoriented_predicates() {
        let interpolants = [
            interpolant(0, "(and (= i@0 n@0) (< i@0 n@0) (= (+ i@0 n@0) x@0))"),
            interpolant(1, "(and (= n@0 i@0) (> n@0 i@0) (= x@0 (+ n@0 i@0)))"),
        ];

        let catalog = PredicateCatalog::from_interpolants(&interpolants);

        assert_eq!(
            candidate_terms(&catalog),
            ["(= i@0 n@0)", "(< i@0 n@0)", "(= (+ i@0 n@0) x@0)"]
        );
        assert!(catalog
            .candidates()
            .iter()
            .all(|candidate| candidate.interpolant_numbers == BTreeSet::from([0, 1])));
    }
}
