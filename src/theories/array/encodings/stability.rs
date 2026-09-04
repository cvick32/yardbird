//! Syntactic proofs that a transition carries state unchanged.
//!
//! A state can be stable even when the transition encodes its carry as a set
//! of guarded assignments instead of one unconditional equality.  We certify
//! those cases only when every assignment carries the current value and the
//! disjunction of assignment guards propositionally covers the transition's
//! top-level current-state constraints.

use std::collections::{HashMap, HashSet};

use smt2parser::concrete::{Identifier, QualIdentifier, Term};

const MAX_COVERAGE_ATOMS: usize = 12;

#[derive(Clone, Debug, Default)]
struct AssignmentScan {
    assignments: Vec<(Option<Term>, Term)>,
    unsupported: bool,
}

/// Return states proven equal to their next-state versions on every enabled
/// transition.
pub(super) fn certified_stable_states(
    transition: &Term,
    current_to_next: &HashMap<String, String>,
) -> HashSet<String> {
    let next_names = current_to_next.values().cloned().collect::<HashSet<_>>();
    let contexts = top_level_conjuncts(transition)
        .into_iter()
        .filter(|term| !contains_any_symbol(term, &next_names))
        .cloned()
        .collect::<Vec<_>>();

    current_to_next
        .iter()
        .filter_map(|(current, next)| {
            let assignments =
                exhaustive_next_assignments_with_context(transition, next, &contexts)?;
            assignments
                .iter()
                .all(|value| simple_symbol(value) == Some(current))
                .then(|| current.clone())
        })
        .collect()
}

/// Return every direct assignment to `next` only when the transition proves
/// that their guards cover all enabled paths and no other use can assign it.
pub(super) fn exhaustive_next_assignments(
    transition: &Term,
    next: &str,
    next_names: &HashSet<String>,
) -> Option<Vec<Term>> {
    let contexts = top_level_conjuncts(transition)
        .into_iter()
        .filter(|term| !contains_any_symbol(term, next_names))
        .cloned()
        .collect::<Vec<_>>();
    exhaustive_next_assignments_with_context(transition, next, &contexts)
}

fn exhaustive_next_assignments_with_context(
    transition: &Term,
    next: &str,
    contexts: &[Term],
) -> Option<Vec<Term>> {
    let mut scan = AssignmentScan::default();
    collect_assignments(transition, next, None, &mut scan);
    let guards = scan
        .assignments
        .iter()
        .map(|(guard, _)| guard.clone())
        .collect::<Vec<_>>();
    if scan.unsupported || guards.is_empty() || !guards_cover_context(contexts, &guards) {
        return None;
    }
    Some(
        scan.assignments
            .into_iter()
            .map(|(_, value)| value)
            .collect(),
    )
}

fn collect_assignments(
    term: &Term,
    next: &str,
    outer_guard: Option<Term>,
    scan: &mut AssignmentScan,
) {
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        if contains_symbol(term, next) {
            scan.unsupported = true;
        }
        return;
    };

    match (qual_identifier.get_name().as_str(), arguments.as_slice()) {
        ("and", arguments) => {
            for argument in arguments {
                collect_assignments(argument, next, outer_guard.clone(), scan);
            }
        }
        ("=>", [guard, consequence]) => {
            let combined_guard = match outer_guard {
                Some(outer) => application("and", vec![outer, guard.clone()]),
                None => guard.clone(),
            };
            collect_assignments(consequence, next, Some(combined_guard), scan);
        }
        ("=", [left, right]) => {
            if simple_symbol(left) == Some(next) {
                scan.assignments.push((outer_guard, right.clone()));
            } else if simple_symbol(right) == Some(next) {
                scan.assignments.push((outer_guard, left.clone()));
            } else if contains_symbol(term, next) {
                scan.unsupported = true;
            }
        }
        _ if contains_symbol(term, next) => scan.unsupported = true,
        _ => {}
    }
}

fn guards_cover_context(contexts: &[Term], guards: &[Option<Term>]) -> bool {
    if guards.iter().any(Option::is_none) {
        return true;
    }
    let guards = guards.iter().filter_map(Option::as_ref).collect::<Vec<_>>();
    let mut atoms = HashSet::new();
    for term in contexts.iter().chain(guards.iter().copied()) {
        collect_boolean_atoms(term, &mut atoms);
    }
    if atoms.len() > MAX_COVERAGE_ATOMS {
        return false;
    }
    let atoms = atoms.into_iter().collect::<Vec<_>>();
    let assignments = 1usize << atoms.len();
    for mask in 0..assignments {
        let valuation = atoms
            .iter()
            .enumerate()
            .map(|(index, atom)| (atom.clone(), mask & (1usize << index) != 0))
            .collect::<HashMap<_, _>>();
        if contexts
            .iter()
            .all(|context| evaluate_boolean(context, &valuation))
            && !guards
                .iter()
                .any(|guard| evaluate_boolean(guard, &valuation))
        {
            return false;
        }
    }
    true
}

fn collect_boolean_atoms(term: &Term, atoms: &mut HashSet<Term>) {
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        if !matches!(simple_symbol(term), Some("true" | "false")) {
            atoms.insert(canonical_atom(term).0);
        }
        return;
    };
    match qual_identifier.get_name().as_str() {
        "and" | "or" | "=>" => {
            for argument in arguments {
                collect_boolean_atoms(argument, atoms);
            }
        }
        "not" if arguments.len() == 1 => collect_boolean_atoms(&arguments[0], atoms),
        _ => {
            atoms.insert(canonical_atom(term).0);
        }
    }
}

fn evaluate_boolean(term: &Term, valuation: &HashMap<Term, bool>) -> bool {
    if simple_symbol(term) == Some("true") {
        return true;
    }
    if simple_symbol(term) == Some("false") {
        return false;
    }
    if let Term::Application {
        qual_identifier,
        arguments,
    } = term
    {
        match qual_identifier.get_name().as_str() {
            "and" => {
                return arguments
                    .iter()
                    .all(|term| evaluate_boolean(term, valuation))
            }
            "or" => {
                return arguments
                    .iter()
                    .any(|term| evaluate_boolean(term, valuation))
            }
            "not" if arguments.len() == 1 => {
                return !evaluate_boolean(&arguments[0], valuation);
            }
            "=>" if arguments.len() == 2 => {
                return !evaluate_boolean(&arguments[0], valuation)
                    || evaluate_boolean(&arguments[1], valuation);
            }
            _ => {}
        }
    }
    let (atom, positive) = canonical_atom(term);
    valuation.get(&atom).copied().unwrap_or(false) == positive
}

/// Normalize complementary integer comparisons into the same propositional
/// atom.  This is deliberately not a general arithmetic prover.
fn canonical_atom(term: &Term) -> (Term, bool) {
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        return (term.clone(), true);
    };
    if qual_identifier.get_name() == "not" && arguments.len() == 1 {
        let (atom, positive) = canonical_atom(&arguments[0]);
        return (atom, !positive);
    }
    let name = qual_identifier.get_name();
    let complement = match name.as_str() {
        ">=" => Some("<"),
        "<=" => Some(">"),
        _ => None,
    };
    match complement {
        Some(name) => (application(name, arguments.clone()), false),
        None => (term.clone(), true),
    }
}

fn top_level_conjuncts(term: &Term) -> Vec<&Term> {
    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } if qual_identifier.get_name() == "and" => arguments.iter().collect(),
        _ => vec![term],
    }
}

fn contains_any_symbol(term: &Term, names: &HashSet<String>) -> bool {
    names.iter().any(|name| contains_symbol(term, name))
}

fn contains_symbol(term: &Term, expected: &str) -> bool {
    match term {
        Term::QualIdentifier(identifier) => identifier.get_name() == expected,
        Term::Application { arguments, .. } => arguments
            .iter()
            .any(|argument| contains_symbol(argument, expected)),
        Term::Let { var_bindings, term } => {
            var_bindings
                .iter()
                .any(|(_, binding)| contains_symbol(binding, expected))
                || contains_symbol(term, expected)
        }
        Term::Lambda { term, .. }
        | Term::Forall { term, .. }
        | Term::Exists { term, .. }
        | Term::Attributes { term, .. } => contains_symbol(term, expected),
        Term::Match { term, cases } => {
            contains_symbol(term, expected)
                || cases
                    .iter()
                    .any(|(_, case)| contains_symbol(case, expected))
        }
        Term::Constant(_) => false,
    }
}

fn application(name: &str, arguments: Vec<Term>) -> Term {
    Term::Application {
        qual_identifier: QualIdentifier::simple(name),
        arguments,
    }
}

fn simple_symbol(term: &Term) -> Option<&str> {
    let Term::QualIdentifier(identifier) = term else {
        return None;
    };
    match identifier {
        QualIdentifier::Simple {
            identifier: Identifier::Simple { symbol },
        } => Some(&symbol.0),
        QualIdentifier::Simple {
            identifier: Identifier::Indexed { .. },
        }
        | QualIdentifier::Sorted { .. } => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mapping() -> HashMap<String, String> {
        HashMap::from([("x".to_string(), "x_next".to_string())])
    }

    #[test]
    fn certifies_exhaustive_guarded_carries() {
        let transition: Term = "(and
            (=> (and (= pc 1) (< i n) (> x 0)) (= x x_next))
            (=> (and (= pc 1) (not (> x 0))) (= x x_next))
            (=> (and (= pc 1) (>= i n)) (= x x_next))
            (=> (and (= pc 2) (< i n)) (= x x_next))
            (=> (and (= pc 2) (not (< i n))) (= x x_next))
            (or (= pc 1) (= pc 2)))"
            .parse()
            .unwrap();

        assert!(certified_stable_states(&transition, &mapping()).contains("x"));
    }

    #[test]
    fn rejects_a_gap_in_guard_coverage() {
        let transition: Term = "(and
            (=> (and (= pc 1) (< i n)) (= x x_next))
            (=> (and (= pc 2) (< i n)) (= x x_next))
            (or (= pc 1) (= pc 2)))"
            .parse()
            .unwrap();

        assert!(!certified_stable_states(&transition, &mapping()).contains("x"));
    }

    #[test]
    fn rejects_any_non_carry_assignment() {
        let transition: Term = "(and
            (=> (< i n) (= x x_next))
            (=> (>= i n) (= (+ x 1) x_next)))"
            .parse()
            .unwrap();

        assert!(!certified_stable_states(&transition, &mapping()).contains("x"));
    }
}
