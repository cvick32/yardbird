use super::tests::{prepared_fixture, prepared_options, PreferLongName};
use super::*;
use crate::terms::language::expr_to_term;

fn request(bindings: &[(&str, &str)]) -> BinderSearchRequest {
    BinderSearchRequest {
        helper: "q".into(),
        phase: SearchPhase::Conflicts,
        bindings: bindings
            .iter()
            .map(|(name, term)| (Symbol((*name).into()), term.parse().unwrap()))
            .collect(),
    }
}

fn page(
    prepared: &mut super::tests::PreparedFixture,
    request: &BinderSearchRequest,
) -> InstantiationBatch {
    prepared
        .candidates(
            |_| Ok("false".into()),
            request,
            |_| PreferLongName,
            prepared_options(),
        )
        .unwrap()
}

#[test]
fn partial_bindings_constrain_enumeration_before_the_page_limit() {
    let mut prepared = prepared_fixture(3, 10);
    let unrestricted = &prepared.compiled.phases[&SearchPhase::Conflicts][0];
    let all = unrestricted.search_with_limit(&prepared.egraph, 10_000);
    assert_eq!(
        all.iter()
            .map(|matched| matched.substs.len())
            .sum::<usize>(),
        1_000
    );
    let fixed = request(&[("x0", "v9"), ("x1", "v8")]);
    let batch = page(&mut prepared, &fixed);
    assert_eq!(batch.search.examined_substitutions, 10);
    assert_eq!(batch.candidates.len(), 10);
    let expressions = batch
        .candidates
        .iter()
        .map(|candidate| expr_to_term(candidate.expression.clone()).to_string())
        .collect::<HashSet<_>>();
    for i in 0..10 {
        assert!(expressions.contains(&format!("(=> (q true) (p v9 v8 v{i}))")));
    }
    assert!(!prepared.can_continue(&fixed));
}

#[test]
fn requests_have_independent_cursors_and_do_not_advance_round_robin() {
    let mut prepared = prepared_fixture(3, 11);
    let first = request(&[("x0", "v0")]);
    let second = request(&[("x0", "v1")]);
    assert_eq!(page(&mut prepared, &first).candidates.len(), 100);
    assert!(prepared.can_continue(&first));
    assert_eq!(page(&mut prepared, &second).candidates.len(), 100);
    assert_eq!(page(&mut prepared, &first).candidates.len(), 21);
    assert!(!prepared.can_continue(&first));
    assert!(prepared.can_continue(&second));
    assert!(page(&mut prepared, &first).candidates.is_empty());
    assert_eq!(
        prepared
            .candidates(
                |_| Ok("false".into()),
                SearchPhase::Conflicts,
                |_| PreferLongName,
                prepared_options()
            )
            .unwrap()
            .candidates
            .len(),
        100
    );
    let mut next_model = prepared_fixture(3, 11);
    assert_eq!(page(&mut next_model, &first).candidates.len(), 100);
}

#[test]
fn bound_witness_survives_equivalent_representatives_and_provenance() {
    let mut prepared = prepared_fixture(2, 3);
    let original = prepared.egraph.lookup_expr(&"v0".parse().unwrap()).unwrap();
    let alias = prepared.egraph.lookup_expr(&"v1".parse().unwrap()).unwrap();
    prepared.egraph.union(original, alias);
    prepared.egraph.rebuild();
    // v0 remains the cheap model-eclass representative. The requested v1 must
    // still appear in the asserted formula and the recorded substitution.
    let fixed = request(&[("x0", "v1")]);
    let batch = page(&mut prepared, &fixed);
    assert_eq!(batch.candidates.len(), 2);
    for candidate in batch.candidates {
        assert!(expr_to_term(candidate.expression)
            .to_string()
            .contains("(p v1 "));
        assert!(candidate
            .provenance
            .relative_substitution()
            .iter()
            .any(|binding| binding.variable == "?binding1" && binding.term == "v1"));
    }
}

#[test]
fn fully_bound_instances_need_neither_helper_matches_nor_domain_enumeration() {
    let mut prepared = prepared_fixture(2, 3);
    prepared.egraph = egg::EGraph::default();
    prepared.egraph.add_expr(&"true".parse().unwrap());
    prepared.egraph.rebuild();
    let mut fixed = request(&[("x0", "v1"), ("x1", "v2")]);
    fixed.phase = SearchPhase::Expand;
    let batch = prepared
        .candidates(
            |_| panic!("expansion does not filter model-satisfied chain links"),
            &fixed,
            |_| PreferLongName,
            prepared_options(),
        )
        .unwrap();
    assert_eq!(batch.search.examined_substitutions, 0);
    assert_eq!(batch.search.rounds, 0);
    assert_eq!(batch.candidates.len(), 1);
    let candidate = &batch.candidates[0];
    assert_eq!(
        expr_to_term(candidate.expression.clone()).to_string(),
        "(=> (q true) (p v1 v2))"
    );
    assert!(!candidate.selected);
    assert!(!candidate.model_violation_verified);
    assert_eq!(candidate.provenance.relative_substitution().len(), 2);
    assert!(!prepared.can_continue(&fixed));
    assert!(page(&mut prepared, &fixed).candidates.is_empty());
}

#[test]
fn specialized_requests_cannot_share_an_unrestricted_obligation_cache_key() {
    let mut prepared = prepared_fixture(1, 2);
    let first = request(&[("x0", "v0")]);
    let second = request(&[("x0", "v1")]);
    assert_eq!(page(&mut prepared, &first).candidates.len(), 1);
    let batch = prepared
        .candidates(
            |term| {
                assert!(term.to_string().contains("(p v1)"));
                Ok("true".into())
            },
            &second,
            |_| -> PreferLongName { panic!("satisfied instances should not be grounded") },
            prepared_options(),
        )
        .unwrap();
    assert!(batch.candidates.is_empty());
}

#[test]
fn supplied_symbols_are_not_recaptured_as_other_pattern_variables() {
    let mut prepared = prepared_fixture(2, 2);
    std::rc::Rc::get_mut(&mut prepared.compiled)
        .unwrap()
        .signatures
        .insert("x1".into(), (vec![], string_to_sort("Int")));
    let symbol = prepared.egraph.add_expr(&"x1".parse().unwrap());
    let sort = prepared.egraph.add(TermLanguage::SortTag("Int".into()));
    prepared.egraph.add(TermLanguage::Domain([sort, symbol]));
    prepared.egraph.rebuild();
    prepared
        .representatives
        .insert(symbol, "x1".parse().unwrap());
    prepared.additional_terms.push("x1".parse().unwrap());
    let batch = page(&mut prepared, &request(&[("x0", "x1")]));
    assert_eq!(batch.candidates.len(), 3);
    assert!(batch
        .candidates
        .iter()
        .all(|candidate| expr_to_term(candidate.expression.clone())
            .to_string()
            .contains("(p x1 ")));
}

#[test]
fn complete_witness_requests_preserve_both_quantifier_directions() {
    for kind in [BinderKind::Forall, BinderKind::Exists] {
        let mut prepared = prepared_fixture(1, 2);
        std::rc::Rc::get_mut(&mut prepared.compiled)
            .unwrap()
            .sources[0]
            .kind = kind;
        let mut fixed = request(&[("unit", "true")]);
        fixed.phase = SearchPhase::Witnesses;
        let batch = page(&mut prepared, &fixed);
        assert_eq!(batch.search.examined_substitutions, 0);
        assert_eq!(batch.candidates.len(), 1);
        assert_eq!(
            expr_to_term(batch.candidates[0].expression.clone()).to_string(),
            match kind {
                BinderKind::Forall => "(=> (not (q true)) (not (p (witness0 true))))",
                BinderKind::Exists => "(=> (q true) (p (witness0 true)))",
                _ => unreachable!(),
            }
        );
    }
}

#[test]
fn requests_validate_names_sorts_duplicates_and_witness_direction() {
    let mut prepared = prepared_fixture(2, 3);
    for (invalid, expected) in [
        (request(&[("no_such_variable", "v0")]), "unknown binding"),
        (request(&[("x0", "true")]), "expects Int, got Bool"),
        (request(&[("x0", "v0"), ("x0", "v1")]), "duplicate binding"),
        (request(&[("unit", "false")]), "dummy capture must be true"),
        (request(&[("x0", "undeclared")]), "unknown sort"),
        (
            BinderSearchRequest {
                helper: "missing".into(),
                ..request(&[])
            },
            "unknown binder",
        ),
        (
            BinderSearchRequest {
                phase: SearchPhase::Witnesses,
                ..request(&[("x0", "v0")])
            },
            "witness requests bind captures",
        ),
    ] {
        let error = prepared
            .candidates(
                |_| unreachable!(),
                &invalid,
                |_| PreferLongName,
                prepared_options(),
            )
            .err()
            .unwrap();
        assert!(error.to_string().contains(expected), "{error}");
    }
}

#[test]
fn real_paxos_witness_chain_is_grounded_without_matching_and_closes_agreement_branch() {
    let source =
        VMTModel::from_path("examples/distributed_protocols/paxos/paxos.encoding.vmt").unwrap();
    let (lowered, plan) = lower_model(source).unwrap();
    let (abstracted, types) = lowered.abstract_array_theory();
    // Identify the actual rules structurally; generated helper numbers are not
    // part of this regression's contract. Path discovery is intentionally not
    // implemented by the matching adapter under test.
    let agreement = plan
        .rules
        .iter()
        .find(|rule| {
            rule.variables.len() == 6 && rule.captures.iter().any(|(name, _)| name.0 == "decision")
        })
        .unwrap();
    let decision = app("decision", vec![]);
    let witness_for_sort = |sort: &Sort| {
        let index = agreement
            .variables
            .iter()
            .position(|(_, bound_sort)| bound_sort == sort)
            .unwrap();
        app(&agreement.witnesses[index], vec![decision.clone()])
    };
    let leaf = plan
        .rules
        .iter()
        .find(|rule| {
            rule.variables.len() == 1
                && rule.captures.iter().any(|(name, _)| name.0 == "decision")
                && rule.body.to_string().starts_with("(= (Read_value_Bool ")
                && rule.body.to_string().ends_with(" false)")
        })
        .unwrap();
    let parent = |child: &BinderRule| {
        plan.rules.iter().find(|rule| matches!(
        &rule.body, Term::Application { qual_identifier, .. } if qual_identifier.get_name() == child.name
    )).unwrap()
    };
    let middle = parent(leaf);
    let outer = parent(middle);
    let mut prepared = prepared_fixture(1, 1);
    prepared.compiled = plan.compiled(&types).unwrap();
    let mut instances = Vec::new();
    for rule in [outer, middle, leaf] {
        let request = BinderSearchRequest {
            helper: rule.name.clone(),
            phase: SearchPhase::Expand,
            bindings: rule
                .captures
                .iter()
                .chain(&rule.variables)
                .map(|(name, sort)| {
                    (
                        name.clone(),
                        if name.0 == "decision" {
                            decision.clone()
                        } else {
                            witness_for_sort(sort)
                        },
                    )
                })
                .collect(),
        };
        let batch = prepared
            .candidates(
                |_| unreachable!(),
                &request,
                |_| PreferLongName,
                prepared_options(),
            )
            .unwrap();
        assert_eq!(batch.search.examined_substitutions, 0);
        assert_eq!(batch.candidates.len(), 1);
        instances.push(expr_to_term(batch.candidates[0].expression.clone()));
    }
    // Replay the real initial condition, and hold the agreement helper false.
    // The witness forces two disagreeing decisions. Each prefix is checked in
    // a fresh solver so declarations remain local to this test.
    let mut declarations = HashSet::new();
    let mut query = abstracted
        .as_commands()
        .into_iter()
        .filter(|command| {
            matches!(
                command,
                Command::DeclareSort { .. } | Command::DeclareFun { .. }
            )
        })
        .map(|command| command.to_string())
        // Lowering and array abstraction can both register the same Read or
        // Write declaration. Match the solver's declaration deduplication.
        .filter(|command| declarations.insert(command.clone()))
        .collect::<Vec<_>>()
        .join("\n");
    query.push_str(&format!(
        "\n(assert {})\n(assert (not ({} decision)))\n(assert {})\n",
        abstracted.get_initial_condition_for_yardbird(),
        agreement.name,
        agreement
            .witness_instance(std::slice::from_ref(&decision))
            .unwrap()
    ));
    for prefix in 0..=3 {
        let solver = z3::Solver::new();
        solver.from_string(query.as_str());
        assert_eq!(
            solver.get_assertions().len(),
            3 + prefix,
            "query must parse completely"
        );
        assert_eq!(
            solver.check(),
            if prefix == 3 {
                z3::SatResult::Unsat
            } else {
                z3::SatResult::Sat
            },
            "chain prefix {prefix}:\n{}",
            query
                .lines()
                .filter(|line| line.starts_with("(assert"))
                .collect::<Vec<_>>()
                .join("\n")
        );
        if let Some(instance) = instances.get(prefix) {
            query.push_str(&format!("(assert {instance})\n"));
        }
    }
}
