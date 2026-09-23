//! Exact read-over-write instances and symbolic alternatives for demanded reads.
//! Both index-equality cases are explored, regardless of the current model.
use crate::transition_index::{leaf_symbol, TransitionIndex};
use crate::{
    rule_matching::candidate::SymbolicInstance,
    rule_matching::rule::QuantifiedRule,
    theories::{array::rule::ArrayAxiomKind, quantifiers::app},
};
use smt2parser::concrete::Term;
use std::collections::HashMap;

pub(crate) fn read_alternatives(
    term: &Term,
    types: &[(String, String)],
    instances: &mut Vec<SymbolicInstance>,
) -> Vec<Term> {
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        return vec![];
    };
    let [array, index] = arguments.as_slice() else {
        return vec![];
    };
    let Some((is, vs)) = types
        .iter()
        .find(|(i, v)| qual_identifier.get_name() == format!("Read_{i}_{v}"))
    else {
        return vec![];
    };
    let Term::Application {
        qual_identifier: head,
        arguments: args,
    } = array
    else {
        return vec![];
    };
    let read = |a: Term, i: Term| app(&format!("Read_{is}_{vs}"), vec![a, i]);
    if head.get_name() == format!("Write_{is}_{vs}") {
        let [base, at, value] = args.as_slice() else {
            return vec![];
        };
        let previous = read(base.clone(), index.clone());
        instances.push(SymbolicInstance {
            rule: QuantifiedRule::array_axiom(ArrayAxiomKind::ReadAfterWrite, is, vs),
            term: app("=", vec![read(array.clone(), at.clone()), value.clone()]),
            bindings: vec![
                ("?a".into(), base.clone()),
                ("?idx".into(), at.clone()),
                ("?val".into(), value.clone()),
            ],
        });
        if index != at {
            instances.push(SymbolicInstance {
                rule: QuantifiedRule::array_axiom(ArrayAxiomKind::WriteDoesNotOverwrite, is, vs),
                term: app(
                    "=>",
                    vec![
                        app("not", vec![app("=", vec![at.clone(), index.clone()])]),
                        app("=", vec![term.clone(), previous.clone()]),
                    ],
                ),
                bindings: vec![
                    ("?a".into(), base.clone()),
                    ("?idx".into(), at.clone()),
                    ("?val".into(), value.clone()),
                    ("?c".into(), index.clone()),
                ],
            });
            return vec![previous, value.clone()];
        }
        return vec![value.clone()];
    }
    if head.get_name() == format!("ConstArr_{is}_{vs}") {
        let [value] = args.as_slice() else {
            return vec![];
        };
        instances.push(SymbolicInstance {
            rule: QuantifiedRule::array_axiom(ArrayAxiomKind::ConstantArray, is, vs),
            term: app("=", vec![term.clone(), value.clone()]),
            bindings: vec![("?a".into(), value.clone()), ("?b".into(), index.clone())],
        });
        return vec![value.clone()];
    }
    vec![]
}

/// One syntactic transport step. Opaque applications (especially witness
/// functions) are never traversed: changing a witness capture changes its value.
#[allow(clippy::too_many_arguments)]
pub(crate) fn transport(
    term: &Term,
    array_position: bool,
    index: &TransitionIndex,
    evaluate: &mut dyn FnMut(&Term) -> anyhow::Result<String>,
    active: &HashMap<u16, Option<String>>,
    types: &[(String, String)],
    instances: &mut Vec<SymbolicInstance>,
    output: &mut Vec<Term>,
    limit: usize,
) {
    if output.len() >= limit {
        return;
    }
    if array_position {
        if let Some(expanded) = index.expand_framed_leaf(term) {
            output.push(expanded);
            return;
        }
        if let Some((name, frame)) =
            leaf_symbol(term).and_then(|s| smt2parser::vmt::split_framed_symbol(&s))
        {
            if let Ok(frame) = u16::try_from(frame) {
                if let Some(previous) = frame.checked_sub(1) {
                    for path in index.update_paths(&name) {
                        if path.action.as_ref().is_some_and(|a| {
                            active.get(&previous).and_then(Option::as_ref) != Some(a)
                        }) {
                            continue;
                        }
                        if path.guards.iter().all(|g| {
                            evaluate(&index.index_term(&g.expression, previous)).is_ok_and(|v| {
                                v.trim() == if g.required_value { "true" } else { "false" }
                            })
                        }) {
                            output.push(index.index_term(&path.value, previous));
                            if output.len() >= limit {
                                break;
                            }
                        }
                    }
                }
            }
        }
    }
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        return;
    };
    let name = qual_identifier.get_name();
    let is_read = types.iter().any(|(i, v)| name == format!("Read_{i}_{v}"));
    output.extend(read_alternatives(term, types, instances));
    if !is_read
        && !matches!(
            name.as_str(),
            "=" | "distinct"
                | "not"
                | "and"
                | "or"
                | "=>"
                | "ite"
                | "<"
                | ">"
                | "<="
                | ">="
                | "+"
                | "-"
                | "*"
        )
    {
        return;
    }
    for (i, arg) in arguments.iter().enumerate() {
        if is_read && i != 0 {
            continue;
        }
        let mut replacements = Vec::new();
        transport(
            arg,
            is_read,
            index,
            evaluate,
            active,
            types,
            instances,
            &mut replacements,
            limit.saturating_sub(output.len()),
        );
        for replacement in replacements {
            let mut args = arguments.clone();
            args[i] = replacement;
            output.push(Term::Application {
                qual_identifier: qual_identifier.clone(),
                arguments: args,
            });
            if output.len() >= limit {
                return;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn transport_preserves_witness_captures_and_obeys_action_branch() {
        let model =
            smt2parser::vmt::VMTModel::from_path("tests/fixtures/array_dataflow_actions.vmt")
                .unwrap();
        let (model, types) = model.abstract_array_theory();
        let index = TransitionIndex::from_model(&model, &HashSet::new());
        let term: Term = "(Read_Int_Int a@2 (witness a@2))".parse().unwrap();
        let mut instances = Vec::new();
        let mut alternatives = Vec::new();
        let mut evaluate = |term: &Term| {
            Ok(if term.to_string() == "choose@1" {
                "false"
            } else {
                "true"
            }
            .into())
        };
        transport(
            &term,
            false,
            &index,
            &mut evaluate,
            &HashMap::from([(1, Some("send".into()))]),
            &types,
            &mut instances,
            &mut alternatives,
            64,
        );
        assert_eq!(
            alternatives,
            vec!["(Read_Int_Int (Write_Int_Int a@1 2 20) (witness a@2))"
                .parse::<Term>()
                .unwrap()]
        );
        let read = alternatives.pop().unwrap();
        alternatives.clear();
        transport(
            &read,
            false,
            &index,
            &mut evaluate,
            &HashMap::new(),
            &types,
            &mut instances,
            &mut alternatives,
            64,
        );
        assert!(alternatives.contains(&"(Read_Int_Int a@1 (witness a@2))".parse().unwrap()));
        assert!(alternatives.contains(&"20".parse().unwrap()));
        assert_eq!(instances.len(), 2);
        assert!(instances
            .iter()
            .any(|i| i.term.to_string().contains("(witness a@2)")));
        assert!(instances
            .iter()
            .all(|i| !i.term.to_string().contains("(witness a@1)")));
    }

    #[test]
    fn both_transport_cases_are_valid_native_array_instances() {
        let types = vec![("Int".into(), "Int".into())];
        for text in [
            "(Read_Int_Int (Write_Int_Int a i v) j)",
            "(Read_Int_Int (Write_Int_Int a i v) i)",
            "(Read_Int_Int (ConstArr_Int_Int v) j)",
        ] {
            let mut instances = Vec::new();
            read_alternatives(&text.parse().unwrap(), &types, &mut instances);
            for instance in instances {
                // Independent semantic oracle: ask native Z3 arrays whether an
                // emitted axiom can be false, with every binding unconstrained.
                let formula = instance
                    .term
                    .to_string()
                    .replace("Read_Int_Int", "select")
                    .replace("Write_Int_Int", "store")
                    .replace("ConstArr_Int_Int", "(as const (Array Int Int))");
                let solver = z3::Solver::new();
                solver.from_string(format!("(declare-const a (Array Int Int)) (declare-const i Int) (declare-const j Int) (declare-const v Int) (assert (not {formula}))"));
                assert_eq!(solver.check(), z3::SatResult::Unsat, "{formula}");
            }
        }
    }
}
