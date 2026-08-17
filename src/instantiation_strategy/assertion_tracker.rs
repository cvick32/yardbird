use rustc_hash::FxHashSet;
use smt2parser::concrete::Term;

use crate::utils::SolverStatistics;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssertionKind {
    IndexedTheory,
    HelperDefinition,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct InstantiationAssertionMetrics {
    pub abstract_instances: u64,
    pub indexed_equality_attempts: u64,
    pub indexed_equality_unique: u64,
    pub indexed_equality_duplicates: u64,
    pub helper_equality_attempts: u64,
    pub helper_equality_unique: u64,
    pub helper_equality_duplicates: u64,
    pub unique_assertions: u64,
    pub all_eligible_frame_placements: u64,
}

impl InstantiationAssertionMetrics {
    pub fn add_to_solver_statistics(self, statistics: &mut SolverStatistics) {
        for (key, value) in [
            ("yardbird.abstract instances", self.abstract_instances),
            (
                "yardbird.indexed equality attempts",
                self.indexed_equality_attempts,
            ),
            (
                "yardbird.indexed equality unique",
                self.indexed_equality_unique,
            ),
            (
                "yardbird.indexed equality duplicates",
                self.indexed_equality_duplicates,
            ),
            (
                "yardbird.instantiation helper equality attempts",
                self.helper_equality_attempts,
            ),
            (
                "yardbird.instantiation helper equality unique",
                self.helper_equality_unique,
            ),
            (
                "yardbird.instantiation helper equality duplicates",
                self.helper_equality_duplicates,
            ),
            (
                "yardbird.unique instantiation assertions",
                self.unique_assertions,
            ),
            (
                "yardbird.all-eligible-frame placements",
                self.all_eligible_frame_placements,
            ),
        ] {
            statistics.add_count(key, value);
        }
    }
}

/// Tracks the post-indexing, post-materialization formulas that Z3 actually
/// receives. Equality orientation is canonicalized only for the deduplication
/// key; the original assertion is preserved when it is sent to the solver.
#[derive(Clone, Debug, Default)]
pub struct InstantiationAssertionTracker {
    seen_ground_equality_formulas: FxHashSet<Term>,
    metrics: InstantiationAssertionMetrics,
}

impl InstantiationAssertionTracker {
    pub fn record_abstract_instance(&mut self) {
        self.metrics.abstract_instances += 1;
    }

    pub fn record_all_eligible_frame_placement(&mut self) {
        self.metrics.all_eligible_frame_placements += 1;
    }

    pub fn accept(&mut self, term: &Term, kind: AssertionKind) -> bool {
        let Some(key) = canonical_ground_equality_formula(term) else {
            self.metrics.unique_assertions += 1;
            return true;
        };

        match kind {
            AssertionKind::IndexedTheory => self.metrics.indexed_equality_attempts += 1,
            AssertionKind::HelperDefinition => self.metrics.helper_equality_attempts += 1,
        }

        if !self.seen_ground_equality_formulas.insert(key) {
            match kind {
                AssertionKind::IndexedTheory => self.metrics.indexed_equality_duplicates += 1,
                AssertionKind::HelperDefinition => self.metrics.helper_equality_duplicates += 1,
            }
            return false;
        }

        match kind {
            AssertionKind::IndexedTheory => self.metrics.indexed_equality_unique += 1,
            AssertionKind::HelperDefinition => self.metrics.helper_equality_unique += 1,
        }
        self.metrics.unique_assertions += 1;
        true
    }

    pub fn metrics(&self) -> InstantiationAssertionMetrics {
        self.metrics
    }
}

/// Canonical key shared by candidate novelty checks and post-materialization
/// solver assertion deduplication.
pub(crate) fn canonical_instantiation_key(term: &Term) -> Term {
    canonical_ground_equality_formula(term).unwrap_or_else(|| term.clone())
}

fn canonical_ground_equality_formula(term: &Term) -> Option<Term> {
    let (canonical, contains_equality, is_ground) = canonicalize_term(term);
    (contains_equality && is_ground).then_some(canonical)
}

fn canonicalize_term(term: &Term) -> (Term, bool, bool) {
    match term {
        Term::Constant(_) | Term::QualIdentifier(_) => (term.clone(), false, true),
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let mut contains_equality = qual_identifier.get_name() == "=";
            let mut is_ground = true;
            let mut canonical_arguments = arguments
                .iter()
                .map(|argument| {
                    let (canonical, argument_contains_equality, argument_is_ground) =
                        canonicalize_term(argument);
                    contains_equality |= argument_contains_equality;
                    is_ground &= argument_is_ground;
                    canonical
                })
                .collect::<Vec<_>>();
            if qual_identifier.get_name() == "="
                && canonical_arguments.len() == 2
                && canonical_arguments[0].to_string() > canonical_arguments[1].to_string()
            {
                canonical_arguments.swap(0, 1);
            }

            (
                Term::Application {
                    qual_identifier: qual_identifier.clone(),
                    arguments: canonical_arguments,
                },
                contains_equality,
                is_ground,
            )
        }
        Term::Let { var_bindings, term } => {
            let mut contains_equality = false;
            let mut is_ground = true;
            let bindings = var_bindings
                .iter()
                .map(|(symbol, value)| {
                    let (canonical, binding_contains_equality, binding_is_ground) =
                        canonicalize_term(value);
                    contains_equality |= binding_contains_equality;
                    is_ground &= binding_is_ground;
                    (symbol.clone(), canonical)
                })
                .collect();
            let (canonical_term, body_contains_equality, body_is_ground) = canonicalize_term(term);
            (
                Term::Let {
                    var_bindings: bindings,
                    term: Box::new(canonical_term),
                },
                contains_equality || body_contains_equality,
                is_ground && body_is_ground,
            )
        }
        Term::Forall { .. } | Term::Exists { .. } => (term.clone(), false, false),
        Term::Match { term, cases } => {
            let (canonical_term, mut contains_equality, mut is_ground) = canonicalize_term(term);
            let cases = cases
                .iter()
                .map(|(symbols, case)| {
                    let (canonical, case_contains_equality, case_is_ground) =
                        canonicalize_term(case);
                    contains_equality |= case_contains_equality;
                    is_ground &= case_is_ground;
                    (symbols.clone(), canonical)
                })
                .collect();
            (
                Term::Match {
                    term: Box::new(canonical_term),
                    cases,
                },
                contains_equality,
                is_ground,
            )
        }
        Term::Attributes { term, attributes } => {
            let (canonical, contains_equality, is_ground) = canonicalize_term(term);
            (
                Term::Attributes {
                    term: Box::new(canonical),
                    attributes: attributes.clone(),
                },
                contains_equality,
                is_ground,
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deduplicates_reversed_ground_equalities() {
        let mut tracker = InstantiationAssertionTracker::default();
        let first: Term = "(= (Read_Int_Int A@2 i@2) v@2)".parse().unwrap();
        let reversed: Term = "(= v@2 (Read_Int_Int A@2 i@2))".parse().unwrap();

        assert!(tracker.accept(&first, AssertionKind::IndexedTheory));
        assert!(!tracker.accept(&reversed, AssertionKind::IndexedTheory));
        assert_eq!(tracker.metrics().indexed_equality_attempts, 2);
        assert_eq!(tracker.metrics().indexed_equality_unique, 1);
        assert_eq!(tracker.metrics().indexed_equality_duplicates, 1);
    }

    #[test]
    fn canonicalizes_equalities_inside_guards_and_consequents() {
        let mut tracker = InstantiationAssertionTracker::default();
        let first: Term = "(=> (not (= i@2 j@2)) (= x@2 y@2))".parse().unwrap();
        let reversed: Term = "(=> (not (= j@2 i@2)) (= y@2 x@2))".parse().unwrap();

        assert!(tracker.accept(&first, AssertionKind::IndexedTheory));
        assert!(!tracker.accept(&reversed, AssertionKind::IndexedTheory));
    }

    #[test]
    fn does_not_deduplicate_quantified_formulas() {
        let mut tracker = InstantiationAssertionTracker::default();
        let quantified: Term = "(forall ((i Int)) (= i i))".parse().unwrap();

        assert!(tracker.accept(&quantified, AssertionKind::IndexedTheory));
        assert!(tracker.accept(&quantified, AssertionKind::IndexedTheory));
        assert_eq!(tracker.metrics().indexed_equality_attempts, 0);
    }
}
