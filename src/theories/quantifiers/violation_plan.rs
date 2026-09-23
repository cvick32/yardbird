//! Bounded Boolean alternatives for one binder body's required model value.
//! Triggered matching uses these over represented terms. Typed-domain fallback
//! can also evaluate their atoms to reject partial tuples; neither replaces the
//! full-instance model check.
use super::*;

const MAX_ALTERNATIVES: usize = 8;
const MAX_ATOMS: usize = 16;
const MAX_WORK: usize = 256;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct SignedAtom {
    pub term: Term,
    pub truth: bool,
}

pub(super) fn plans(rule: &BinderRule) -> Option<Vec<Vec<SignedAtom>>> {
    if rule.kind == BinderKind::Lambda {
        return None;
    }
    let mut work = MAX_WORK;
    boolean(&rule.body, rule.kind == BinderKind::Exists, &mut work)
}

fn boolean(term: &Term, truth: bool, work: &mut usize) -> Option<Vec<Vec<SignedAtom>>> {
    *work = work.checked_sub(1)?;
    if contains_binders(term) || unsupported(term) {
        return None;
    }
    if let Term::QualIdentifier(id) = term {
        if matches!(id.get_name().as_str(), "true" | "false") {
            return Some(if (id.get_name() == "true") == truth {
                vec![vec![]]
            } else {
                vec![]
            });
        }
    }
    if let Term::Application {
        qual_identifier,
        arguments,
    } = term
    {
        match (qual_identifier.get_name().as_str(), arguments.as_slice()) {
            ("not", [inner]) => return boolean(inner, !truth, work),
            ("=>", [a, b]) => {
                let a = boolean(a, !truth, work)?;
                let b = boolean(b, truth, work)?;
                return combine(a, b, !truth);
            }
            ("and" | "or", children) => {
                let product = (qual_identifier.get_name() == "and") == truth;
                let mut result = if product { vec![vec![]] } else { vec![] };
                for child in children {
                    result = combine(result, boolean(child, truth, work)?, product)?;
                }
                return Some(result);
            }
            ("=", [a, b]) => {
                for (atom, value) in [(a, b), (b, a)] {
                    if let Term::QualIdentifier(id) = value {
                        if matches!(id.get_name().as_str(), "true" | "false") {
                            return boolean(atom, truth == (id.get_name() == "true"), work);
                        }
                    }
                }
            }
            _ => {}
        }
    }
    Some(vec![vec![SignedAtom {
        term: term.clone(),
        truth,
    }]])
}

fn unsupported(term: &Term) -> bool {
    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let name = qual_identifier.get_name();
            matches!(name.as_str(), "ite" | "xor" | "distinct")
                || name.starts_with("__yardbird_quantifier_")
                || arguments.iter().any(unsupported)
        }
        Term::QualIdentifier(_) | Term::Constant(_) => false,
        _ => true,
    }
}

fn combine(
    a: Vec<Vec<SignedAtom>>,
    b: Vec<Vec<SignedAtom>>,
    product: bool,
) -> Option<Vec<Vec<SignedAtom>>> {
    let size = if product {
        a.len().checked_mul(b.len())?
    } else {
        a.len().checked_add(b.len())?
    };
    if size > MAX_ALTERNATIVES {
        return None;
    }
    if !product {
        return Some(a.into_iter().chain(b).collect());
    }
    let mut result = Vec::new();
    for left in a {
        for right in &b {
            let mut atoms = left.clone();
            let mut contradiction = false;
            for atom in right {
                if atoms
                    .iter()
                    .any(|old| old.term == atom.term && old.truth != atom.truth)
                {
                    contradiction = true;
                    break;
                }
                if !atoms.contains(atom) {
                    atoms.push(atom.clone());
                }
            }
            if !contradiction {
                if atoms.len() > MAX_ATOMS {
                    return None;
                }
                result.push(atoms);
            }
        }
    }
    Some(result)
}

/// Equality and comparison operands may be represented even when the Boolean
/// expression itself is absent. Evaluate these after joins instead of requiring
/// an equality/comparison node in the graph.
pub(super) fn is_filter(atom: &SignedAtom) -> bool {
    matches!(&atom.term, Term::Application { qual_identifier, .. }
        if matches!(qual_identifier.get_name().as_str(), "=" | "<" | "<=" | ">" | ">="))
}

#[cfg(test)]
mod tests {
    use super::super::tests::{prepared_fixture, prepared_options, PreferLongName};
    use super::*;

    fn rule(body: &str) -> BinderRule {
        BinderRule {
            name: "q".into(),
            kind: BinderKind::Forall,
            captures: vec![(Symbol("unit".into()), string_to_sort("Bool"))],
            variables: (0..4)
                .map(|i| (Symbol(format!("x{i}")), string_to_sort("Int")))
                .collect(),
            body: body.parse().unwrap(),
            witnesses: (0..4).map(|i| format!("w{i}")).collect(),
            result_sort: string_to_sort("Bool"),
            unit_capture: true,
        }
    }

    fn eval(t: &Term, assignment: usize) -> bool {
        if let Term::QualIdentifier(id) = t {
            return match id.get_name().as_str() {
                "true" => true,
                "false" => false,
                "a" => assignment & 1 != 0,
                "b" => assignment & 2 != 0,
                "c" => assignment & 4 != 0,
                name => panic!("unexpected atom {name}"),
            };
        }
        let Term::Application {
            qual_identifier,
            arguments: a,
        } = t
        else {
            panic!()
        };
        match qual_identifier.get_name().as_str() {
            "not" => !eval(&a[0], assignment),
            "and" => a.iter().all(|t| eval(t, assignment)),
            "or" => a.iter().any(|t| eval(t, assignment)),
            "=>" => !eval(&a[0], assignment) || eval(&a[1], assignment),
            "=" => eval(&a[0], assignment) == eval(&a[1], assignment),
            _ => panic!(),
        }
    }

    #[test]
    fn alternatives_preserve_both_truth_directions() {
        for formula in [
            "(=> (and a b) c)",
            "(=> a (and (not b) (not c)))",
            "(=> (and a (not b)) (or b c))",
            "(and (=> a b) (=> b c))",
            "(or (not (and a b)) c)",
            "(= (and a b) false)",
            "(not (not a))",
            "true",
            "false",
            "(and a (not a))",
            "(= a b)",
        ] {
            for kind in [BinderKind::Forall, BinderKind::Exists] {
                let mut rule = rule(formula);
                rule.kind = kind;
                let alternatives = plans(&rule).unwrap();
                for assignment in 0..8 {
                    assert_eq!(
                        alternatives.iter().any(|atoms| atoms
                            .iter()
                            .all(|a| eval(&a.term, assignment) == a.truth)),
                        eval(&rule.body, assignment) == (kind == BinderKind::Exists),
                        "{formula} {kind:?} {assignment}"
                    );
                }
            }
        }
    }

    #[test]
    fn unsupported_shapes_and_excessive_alternatives_use_fallback() {
        for body in [
            "(ite a b c)",
            "(forall ((z Int)) (p z))",
            "(__yardbird_quantifier_1 x0)",
            "(xor a b)",
        ] {
            assert!(plans(&rule(body)).is_none(), "{body}");
        }
        let body = format!(
            "(and {})",
            (0..9)
                .map(|i| format!("(p x{i})"))
                .collect::<Vec<_>>()
                .join(" ")
        );
        assert!(plans(&rule(&body)).is_none());
        let body = format!(
            "(or {})",
            (0..17)
                .map(|i| format!("(p x{i})"))
                .collect::<Vec<_>>()
                .join(" ")
        );
        assert!(plans(&rule(&body)).is_none());
    }

    fn fixture(
        body: &str,
        atoms: &[(&str, bool)],
    ) -> crate::theories::quantifiers::tests::PreparedFixture {
        fixture_with_size(body, atoms, 20)
    }

    fn fixture_with_size(
        body: &str,
        atoms: &[(&str, bool)],
        size: usize,
    ) -> crate::theories::quantifiers::tests::PreparedFixture {
        let mut prepared = prepared_fixture(4, size);
        let plan = QuantifierPlan {
            rules: vec![rule(body)],
            ..Default::default()
        };
        prepared.compiled = plan.compiled(&[]).unwrap();
        for (term, truth) in atoms {
            let expression =
                crate::terms::language::translate_term_with_array_types(term.parse().unwrap(), &[])
                    .unwrap();
            let id = prepared.egraph.add_expr(&expression);
            let value = prepared
                .egraph
                .lookup_expr(&truth.to_string().parse().unwrap())
                .unwrap();
            prepared.egraph.union(id, value);
            prepared.additional_terms.push(expression);
        }
        prepared.egraph.rebuild();
        prepared.representatives.clear();
        for expression in &prepared.search.additional_terms {
            let id = prepared
                .egraph
                .find(prepared.egraph.lookup_expr(expression).unwrap());
            prepared
                .search
                .representatives
                .entry(id)
                .or_insert(expression.clone());
        }
        prepared
    }

    #[test]
    fn domain_fallback_prunes_missing_predicates_before_full_construction() {
        let mut prepared = fixture("(=> (and (p x0 x1) (p x2 x3)) (= x1 x3))", &[]);
        let mut full_formulas = HashSet::new();
        let mut visited = 0;
        let mut candidates = HashSet::new();
        loop {
            let batch = prepared
                .candidates(
                    |term| {
                        let Term::Application {
                            qual_identifier,
                            arguments,
                        } = term
                        else {
                            panic!()
                        };
                        match qual_identifier.get_name().as_str() {
                            "p" | "=" => Ok((arguments[0] == arguments[1]).to_string()),
                            "=>" => {
                                full_formulas.insert(term.to_string());
                                Ok("false".into())
                            }
                            other => panic!("unexpected atom {other}"),
                        }
                    },
                    SearchPhase::Conflicts,
                    |_| PreferLongName,
                    prepared_options(),
                )
                .unwrap();
            visited += batch.search.examined_substitutions;
            assert!(batch.search.examined_substitutions <= 100);
            assert!(batch.search.budget_exhausted_rules.is_empty());
            for candidate in batch.candidates {
                assert!(candidate.model_violation_verified);
                assert!(candidates.insert(
                    crate::terms::language::expr_to_term(candidate.expression).to_string()
                ));
            }
            if !prepared.can_continue(SearchPhase::Conflicts) {
                break;
            }
        }
        // All 20*19 violating pairs survive, despite no p applications existing
        // in the graph. The old fallback constructs up to 20^4 formulas.
        assert_eq!(candidates.len(), 380);
        assert_eq!(full_formulas.len(), 380);
        assert!(visited < 16_000, "visited {visited} prefixes");
    }

    #[test]
    fn unresolved_partial_conditions_still_require_full_model_validation() {
        let mut prepared = fixture_with_size("(=> (p x0 x1) (r x2 x3))", &[], 3);
        let mut constructions = 0;
        loop {
            let batch = prepared
                .candidates(
                    |term| {
                        if term.to_string().starts_with("(=>") {
                            constructions += 1;
                            Ok("true".into())
                        } else {
                            Ok("unresolved".into())
                        }
                    },
                    SearchPhase::Conflicts,
                    |_| PreferLongName,
                    prepared_options(),
                )
                .unwrap();
            assert!(batch.candidates.is_empty());
            assert!(batch.search.budget_exhausted_rules.is_empty());
            if !prepared.can_continue(SearchPhase::Conflicts) {
                break;
            }
        }
        assert_eq!(constructions, 81);
    }

    #[test]
    fn agreement_joins_true_tuples_and_checks_values_before_full_construction() {
        let mut prepared = fixture(
            "(=> (and (p x0 x1) (p x2 x3)) (= x1 x3))",
            &[
                ("(p v0 v1)", true),
                ("(p v2 v3)", true),
                ("(p v4 v5)", false),
            ],
        );
        let baseline = &prepared.compiled.phases[&SearchPhase::Conflicts][0];
        assert_eq!(
            baseline
                .search_with_limit(&prepared.egraph, 200_000)
                .iter()
                .map(|m| m.substs.len())
                .sum::<usize>(),
            160_000
        );
        let mut evaluated = Vec::new();
        let batch = prepared
            .candidates(
                |term| {
                    evaluated.push(term.to_string());
                    if let Term::Application {
                        qual_identifier,
                        arguments,
                    } = term
                    {
                        if qual_identifier.get_name() == "=" {
                            return Ok((arguments[0] == arguments[1]).to_string());
                        }
                    }
                    Ok("false".into())
                },
                SearchPhase::TriggeredConflicts,
                |_| PreferLongName,
                prepared_options(),
            )
            .unwrap();
        assert_eq!(batch.search.examined_substitutions, 4);
        assert_eq!(batch.candidates.len(), 2);
        assert!(evaluated
            .iter()
            .filter(|t| t.starts_with("(=>"))
            .all(|t| !t.contains("v4")
                && !t.contains("v5")
                && !t.contains("(= v1 v1)")
                && !t.contains("(= v3 v3)")));
        assert!(batch.candidates.iter().all(|c| c.model_violation_verified));
    }

    #[test]
    fn negative_matches_require_explicit_model_false_and_missing_terms_fall_back() {
        let body = "(=> (p x0 x1) (r x2 x3))";
        let mut prepared = fixture(
            body,
            &[
                ("(p v0 v1)", true),
                ("(r v2 v3)", false),
                ("(r v4 v5)", true),
            ],
        );
        let batch = prepared
            .candidates(
                |_| Ok("false".into()),
                SearchPhase::TriggeredConflicts,
                |_| PreferLongName,
                prepared_options(),
            )
            .unwrap();
        assert_eq!(batch.candidates.len(), 1);
        let mut missing = fixture(body, &[("(p v0 v1)", true)]);
        let batch = missing
            .candidates(
                |_| panic!("missing reads are not false"),
                SearchPhase::TriggeredConflicts,
                |_| PreferLongName,
                prepared_options(),
            )
            .unwrap();
        assert!(batch.candidates.is_empty());
        let fallback = missing
            .candidates(
                |term| Ok(term.to_string().starts_with("(p ").to_string()),
                SearchPhase::Conflicts,
                |_| PreferLongName,
                prepared_options(),
            )
            .unwrap();
        assert!(!fallback.candidates.is_empty());
        assert!(fallback.candidates.len() <= 100);
        assert!(missing.can_continue(SearchPhase::Conflicts));
    }

    #[test]
    fn alternatives_have_separate_cursors_and_do_not_require_both_violations() {
        let mut prepared = fixture(
            "(and (=> (p x0 x1) (r x2 x3)) (=> (p x0 x1) (s x2 x3)))",
            &[
                ("(p v0 v1)", true),
                ("(r v2 v3)", false),
                ("(s v4 v5)", false),
            ],
        );
        assert_eq!(
            prepared.compiled.phases[&SearchPhase::TriggeredConflicts].len(),
            2
        );
        for _ in 0..2 {
            let batch = prepared
                .candidates(
                    |_| Ok("false".into()),
                    SearchPhase::TriggeredConflicts,
                    |_| PreferLongName,
                    prepared_options(),
                )
                .unwrap();
            assert_eq!(batch.candidates.len(), 1);
        }
        assert!(!prepared.can_continue(SearchPhase::TriggeredConflicts));
    }

    #[test]
    fn early_filtering_preserves_paging_and_model_refresh() {
        let atoms = (0..20)
            .map(|i| (format!("(p v{i} v{i})"), true))
            .collect::<Vec<_>>();
        let borrowed = atoms
            .iter()
            .map(|(s, b)| (s.as_str(), *b))
            .collect::<Vec<_>>();
        let body = "(=> (and (p x0 x1) (p x2 x3)) (= x1 x3))";
        let mut prepared = fixture(body, &borrowed);
        let mut total = 0;
        let mut pages = 0;
        loop {
            let batch = prepared
                .candidates(
                    |term| {
                        if let Term::Application {
                            qual_identifier,
                            arguments,
                        } = term
                        {
                            if qual_identifier.get_name() == "=" {
                                return Ok((arguments[0] == arguments[1]).to_string());
                            }
                        }
                        Ok("false".into())
                    },
                    SearchPhase::TriggeredConflicts,
                    |_| PreferLongName,
                    prepared_options(),
                )
                .unwrap();
            total += batch.candidates.len();
            pages += 1;
            if !prepared.can_continue(SearchPhase::TriggeredConflicts) {
                break;
            }
            assert!(pages < 5);
        }
        assert_eq!(pages, 4);
        assert_eq!(total, 380);
        let mut refreshed = fixture(body, &[("(p v0 v0)", false)]);
        let batch = refreshed
            .candidates(
                |_| panic!("no true decisions in refreshed model"),
                SearchPhase::TriggeredConflicts,
                |_| PreferLongName,
                prepared_options(),
            )
            .unwrap();
        assert!(batch.candidates.is_empty());
    }
}
