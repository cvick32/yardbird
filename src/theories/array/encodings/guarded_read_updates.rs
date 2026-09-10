//! Guard-preserving, transition-local consequences of array writes.
//!
//! Array abstraction represents `Read` and `Write` as uninterpreted functions.
//! A transition such as `guard => Write(a, i, v) = a_next` then requires Z3 to
//! recover every useful fact about `Read(a_next, ...)` through congruence and
//! separately asserted array axioms. The formulas produced here are redundant
//! consequences of that transition and the array theory, but state the useful
//! read updates directly while retaining the original action guard.

use std::collections::{HashMap, HashSet};

use smt2parser::{
    concrete::{QualIdentifier, Term},
    vmt::VMTModel,
};

#[derive(Clone, Debug)]
struct GuardedWrite {
    guard: Option<Term>,
    read_name: String,
    base: Term,
    index: Term,
    value: Term,
    target: Term,
}

#[derive(Clone, Debug, Default)]
pub(super) struct GuardedReadUpdatePlan {
    pub(super) updates: Vec<Term>,
    pub(super) eager_updates: Vec<Term>,
    pub(super) writes_detected: usize,
    pub(super) writes_rejected_nonlinear: usize,
    pub(super) writes_rejected_expensive: usize,
    pub(super) eager_read_composite_writes: usize,
}

/// Discover transition-local read consequences without adding them eagerly.
///
/// In conservative mode nonlinear write values are omitted. Other expensive
/// values retain only their direct write-index consequence: repeating them
/// inside tracked-index `ite`s can dominate Z3's search, while the direct
/// equality exposes read-after-write without duplicating the value.
pub(super) fn plan_guarded_read_updates(
    model: &VMTModel,
    conservative_values: bool,
) -> GuardedReadUpdatePlan {
    let transition = model.get_trans_condition_for_yardbird();
    let property = model.get_property_for_yardbird();
    let current_to_next = model
        .get_state_variables()
        .into_iter()
        .map(|variable| {
            (
                variable.get_current_variable_name().clone(),
                variable.get_next_variable_name().clone(),
            )
        })
        .collect();
    guarded_read_update_plan(
        &transition,
        &property,
        &current_to_next,
        conservative_values,
    )
}

#[cfg(test)]
fn guarded_read_updates(
    transition: &Term,
    property: &Term,
    current_to_next: &HashMap<String, String>,
) -> Vec<Term> {
    guarded_read_update_plan(transition, property, current_to_next, false).updates
}

fn guarded_read_update_plan(
    transition: &Term,
    property: &Term,
    current_to_next: &HashMap<String, String>,
    conservative_values: bool,
) -> GuardedReadUpdatePlan {
    let mut property_indices = HashMap::<String, HashSet<Term>>::new();
    collect_read_indices(property, &mut property_indices);

    let mut writes = Vec::new();
    collect_guarded_writes(transition, None, &mut writes);
    let assignments = collect_guarded_assignments(transition, current_to_next);

    let writes_detected = writes.len();
    let writes_rejected_nonlinear = if conservative_values {
        writes
            .iter()
            .filter(|write| contains_genuinely_nonlinear_arithmetic(&write.value))
            .count()
    } else {
        0
    };
    let writes_rejected_expensive = if conservative_values {
        writes
            .iter()
            .filter(|write| {
                !contains_genuinely_nonlinear_arithmetic(&write.value)
                    && !is_cheap_read_update_value(&write.value)
            })
            .count()
    } else {
        0
    };
    let mut updates = HashSet::new();
    let mut eager_updates = HashSet::new();
    let mut eager_read_composite_writes = 0;
    for write in writes {
        if conservative_values && contains_genuinely_nonlinear_arithmetic(&write.value) {
            continue;
        }
        let direct_read = read(&write.read_name, write.target.clone(), write.index.clone());
        let direct_update = with_guard(
            write.guard.clone(),
            equals(direct_read, write.value.clone()),
        );
        let eager_read_composite = conservative_values
            && !is_cheap_read_update_value(&write.value)
            && is_small_self_read_composite(&write.value, &write.read_name, &write.base);
        if eager_read_composite {
            eager_read_composite_writes += 1;
        }
        if conservative_values && !is_cheap_read_update_value(&write.value) && !eager_read_composite
        {
            eager_updates.insert(direct_update);
            continue;
        }
        let selected_updates = if eager_read_composite {
            &mut eager_updates
        } else {
            &mut updates
        };
        selected_updates.insert(direct_update);

        if let Some(indices) = property_indices.get(&write.read_name) {
            for tracked_index in indices {
                insert_tracked_update(
                    selected_updates,
                    &write,
                    tracked_index,
                    false,
                    current_to_next,
                    &assignments,
                );
            }
        }
        let mut transition_indices = HashSet::new();
        collect_read_indices_for_array(
            transition,
            &write.read_name,
            &write.base,
            &mut transition_indices,
        );
        for tracked_index in transition_indices {
            insert_tracked_update(
                selected_updates,
                &write,
                &tracked_index,
                true,
                current_to_next,
                &assignments,
            );
        }
    }

    let mut updates = updates.into_iter().collect::<Vec<_>>();
    updates.sort_by_key(ToString::to_string);
    let mut eager_updates = eager_updates.into_iter().collect::<Vec<_>>();
    eager_updates.sort_by_key(ToString::to_string);
    GuardedReadUpdatePlan {
        updates,
        eager_updates,
        writes_detected,
        writes_rejected_nonlinear,
        writes_rejected_expensive,
        eager_read_composite_writes,
    }
}

fn contains_genuinely_nonlinear_arithmetic(term: &Term) -> bool {
    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let nonlinear_here = qual_identifier.get_name() == "*"
                && arguments
                    .iter()
                    .filter(|argument| !is_integer_constant(argument))
                    .count()
                    > 1;
            nonlinear_here
                || arguments
                    .iter()
                    .any(contains_genuinely_nonlinear_arithmetic)
        }
        Term::Let { var_bindings, term } => {
            var_bindings
                .iter()
                .any(|(_, binding)| contains_genuinely_nonlinear_arithmetic(binding))
                || contains_genuinely_nonlinear_arithmetic(term)
        }
        Term::Lambda { term, .. }
        | Term::Forall { term, .. }
        | Term::Exists { term, .. }
        | Term::Attributes { term, .. } => contains_genuinely_nonlinear_arithmetic(term),
        Term::Match { term, cases } => {
            contains_genuinely_nonlinear_arithmetic(term)
                || cases
                    .iter()
                    .any(|(_, case)| contains_genuinely_nonlinear_arithmetic(case))
        }
        Term::Constant(_) | Term::QualIdentifier(_) => false,
    }
}

fn is_integer_constant(term: &Term) -> bool {
    match term {
        Term::Constant(smt2parser::concrete::Constant::Numeral(_)) => true,
        Term::Application {
            qual_identifier,
            arguments,
        } if qual_identifier.get_name() == "-" && arguments.len() == 1 => {
            is_integer_constant(&arguments[0])
        }
        _ => false,
    }
}

const MAX_CHEAP_SCALAR_AFFINE_NODES: usize = 7;
const MAX_EAGER_READ_COMPOSITE_NODES: usize = 9;

/// Cheap values avoid cloning general arithmetic into every tracked read
/// consequence. Read indices are deliberately opaque here: index arithmetic
/// does not become part of the stored value and was beneficial for inverse-copy
/// benchmarks in the validation cohort. Small scalar-affine values are also
/// cheap, while additive expressions containing reads remain excluded.
pub(super) fn is_cheap_read_update_value(term: &Term) -> bool {
    if matches!(
        scalar_affine_node_count(term),
        Some(nodes) if nodes <= MAX_CHEAP_SCALAR_AFFINE_NODES
    ) {
        return true;
    }

    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } if qual_identifier.get_name().starts_with("Read_") && arguments.len() == 2 => true,
        Term::Application {
            qual_identifier,
            arguments,
        } if qual_identifier.get_name() == "*" && arguments.len() == 2 => {
            (is_integer_constant(&arguments[0]) && is_cheap_read_update_value(&arguments[1]))
                || (is_integer_constant(&arguments[1]) && is_cheap_read_update_value(&arguments[0]))
        }
        _ => false,
    }
}

fn scalar_affine_node_count(term: &Term) -> Option<usize> {
    match term {
        Term::Constant(_) | Term::QualIdentifier(_) => Some(1),
        Term::Application {
            qual_identifier,
            arguments,
        } if matches!(qual_identifier.get_name().as_str(), "+" | "-") && !arguments.is_empty() => {
            arguments.iter().try_fold(1usize, |nodes, argument| {
                nodes.checked_add(scalar_affine_node_count(argument)?)
            })
        }
        Term::Application {
            qual_identifier,
            arguments,
        } if qual_identifier.get_name() == "*" && arguments.len() == 2 => {
            if is_integer_constant(&arguments[0]) {
                scalar_affine_node_count(&arguments[1])?.checked_add(1)
            } else if is_integer_constant(&arguments[1]) {
                scalar_affine_node_count(&arguments[0])?.checked_add(1)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn is_small_self_read_composite(term: &Term, read_name: &str, base: &Term) -> bool {
    fn scan(term: &Term) -> Option<(usize, bool)> {
        match term {
            Term::Constant(_) | Term::QualIdentifier(_) => Some((1, false)),
            Term::Application {
                qual_identifier,
                arguments,
            } if qual_identifier.get_name().starts_with("Read_") && arguments.len() == 2 => {
                let nodes = arguments.iter().try_fold(1usize, |nodes, argument| {
                    nodes.checked_add(scan(argument)?.0)
                })?;
                Some((nodes, true))
            }
            Term::Application {
                qual_identifier,
                arguments,
            } if matches!(qual_identifier.get_name().as_str(), "+" | "-")
                && !arguments.is_empty() =>
            {
                arguments
                    .iter()
                    .try_fold((1usize, false), |(nodes, saw_read), argument| {
                        let (argument_nodes, argument_saw_read) = scan(argument)?;
                        Some((
                            nodes.checked_add(argument_nodes)?,
                            saw_read || argument_saw_read,
                        ))
                    })
            }
            Term::Application {
                qual_identifier,
                arguments,
            } if qual_identifier.get_name() == "*" && arguments.len() == 2 => {
                if is_integer_constant(&arguments[0]) {
                    let (nodes, saw_read) = scan(&arguments[1])?;
                    Some((nodes.checked_add(2)?, saw_read))
                } else if is_integer_constant(&arguments[1]) {
                    let (nodes, saw_read) = scan(&arguments[0])?;
                    Some((nodes.checked_add(2)?, saw_read))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    matches!(scan(term), Some((nodes, true)) if nodes <= MAX_EAGER_READ_COMPOSITE_NODES)
        && contains_read_from_array(term, read_name, base)
}

fn contains_read_from_array(term: &Term, read_name: &str, base: &Term) -> bool {
    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            (qual_identifier.get_name() == read_name
                && arguments.len() == 2
                && &arguments[0] == base)
                || arguments
                    .iter()
                    .any(|argument| contains_read_from_array(argument, read_name, base))
        }
        Term::Let { var_bindings, term } => {
            var_bindings
                .iter()
                .any(|(_, binding)| contains_read_from_array(binding, read_name, base))
                || contains_read_from_array(term, read_name, base)
        }
        Term::Lambda { term, .. }
        | Term::Forall { term, .. }
        | Term::Exists { term, .. }
        | Term::Attributes { term, .. } => contains_read_from_array(term, read_name, base),
        Term::Match { term, cases } => {
            contains_read_from_array(term, read_name, base)
                || cases
                    .iter()
                    .any(|(_, case)| contains_read_from_array(case, read_name, base))
        }
        Term::Constant(_) | Term::QualIdentifier(_) => false,
    }
}

fn insert_tracked_update(
    updates: &mut HashSet<Term>,
    write: &GuardedWrite,
    tracked_index: &Term,
    shift_index: bool,
    current_to_next: &HashMap<String, String>,
    assignments: &HashMap<String, Vec<GuardedAssignment>>,
) {
    let target_index = if shift_index {
        replace_symbols(tracked_index, current_to_next)
    } else {
        tracked_index.clone()
    };
    let old_index = if shift_index {
        resolve_assignments(target_index.clone(), write.guard.as_ref(), assignments)
    } else {
        tracked_index.clone()
    };
    if target_index == write.index && old_index == write.index {
        return;
    }
    let target_read = read(&write.read_name, write.target.clone(), target_index);
    let old_read = read(&write.read_name, write.base.clone(), old_index.clone());
    let value = application(
        "ite",
        vec![
            equals(old_index, write.index.clone()),
            write.value.clone(),
            old_read,
        ],
    );
    updates.insert(with_guard(write.guard.clone(), equals(target_read, value)));
}

#[derive(Clone, Debug)]
struct GuardedAssignment {
    guard: Option<Term>,
    value: Term,
}

fn collect_guarded_assignments(
    transition: &Term,
    current_to_next: &HashMap<String, String>,
) -> HashMap<String, Vec<GuardedAssignment>> {
    let next_names = current_to_next.values().cloned().collect::<HashSet<_>>();
    let mut assignments = HashMap::<String, Vec<GuardedAssignment>>::new();
    collect_assignments(transition, None, &next_names, &mut assignments);
    assignments
}

fn collect_assignments(
    term: &Term,
    guard: Option<Term>,
    next_names: &HashSet<String>,
    assignments: &mut HashMap<String, Vec<GuardedAssignment>>,
) {
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        return;
    };

    match (qual_identifier.get_name().as_str(), arguments.as_slice()) {
        ("and", arguments) => {
            for argument in arguments {
                collect_assignments(argument, guard.clone(), next_names, assignments);
            }
        }
        ("=>", [antecedent, consequent]) => {
            let guard = Some(match guard {
                Some(outer) => application("and", vec![outer, antecedent.clone()]),
                None => antecedent.clone(),
            });
            collect_assignments(consequent, guard, next_names, assignments);
        }
        ("=", [left, right]) => {
            record_assignment(left, right, guard.clone(), next_names, assignments);
            record_assignment(right, left, guard, next_names, assignments);
        }
        _ => {}
    }
}

fn record_assignment(
    target: &Term,
    value: &Term,
    guard: Option<Term>,
    next_names: &HashSet<String>,
    assignments: &mut HashMap<String, Vec<GuardedAssignment>>,
) {
    let Some(name) = simple_symbol(target) else {
        return;
    };
    if !next_names.contains(name) {
        return;
    }
    assignments
        .entry(name.to_string())
        .or_default()
        .push(GuardedAssignment {
            guard,
            value: value.clone(),
        });
}

fn resolve_assignments(
    term: Term,
    guard: Option<&Term>,
    assignments: &HashMap<String, Vec<GuardedAssignment>>,
) -> Term {
    let replacements = assignments
        .iter()
        .filter_map(|(name, choices)| {
            choices
                .iter()
                .find(|assignment| assignment.guard.as_ref() == guard)
                .or_else(|| choices.iter().find(|assignment| assignment.guard.is_none()))
                .map(|assignment| (name.clone(), assignment.value.clone()))
        })
        .collect();
    replace_terms(&term, &replacements)
}

fn collect_read_indices_for_array(
    term: &Term,
    read_name: &str,
    array: &Term,
    indices: &mut HashSet<Term>,
) {
    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            if qual_identifier.get_name() == read_name
                && arguments.len() == 2
                && &arguments[0] == array
            {
                indices.insert(arguments[1].clone());
            }
            for argument in arguments {
                collect_read_indices_for_array(argument, read_name, array, indices);
            }
        }
        Term::Let { var_bindings, term } => {
            for (_, binding) in var_bindings {
                collect_read_indices_for_array(binding, read_name, array, indices);
            }
            collect_read_indices_for_array(term, read_name, array, indices);
        }
        // Bound indices cannot be evaluated as ground model terms and must
        // not become lazy read-update schemas.
        Term::Lambda { .. } | Term::Forall { .. } | Term::Exists { .. } => {}
        Term::Attributes { term, .. } => {
            collect_read_indices_for_array(term, read_name, array, indices)
        }
        Term::Match { term, .. } => {
            collect_read_indices_for_array(term, read_name, array, indices);
        }
        Term::Constant(_) | Term::QualIdentifier(_) => {}
    }
}

fn simple_symbol(term: &Term) -> Option<&str> {
    let Term::QualIdentifier(identifier) = term else {
        return None;
    };
    match identifier {
        QualIdentifier::Simple { identifier } => match identifier {
            smt2parser::concrete::Identifier::Simple { symbol } => Some(&symbol.0),
            smt2parser::concrete::Identifier::Indexed { .. } => None,
        },
        QualIdentifier::Sorted { .. } => None,
    }
}

fn replace_symbols(term: &Term, replacements: &HashMap<String, String>) -> Term {
    let replacements = replacements
        .iter()
        .map(|(name, replacement)| {
            (
                name.clone(),
                Term::QualIdentifier(QualIdentifier::simple(replacement)),
            )
        })
        .collect();
    replace_terms(term, &replacements)
}

fn replace_terms(term: &Term, replacements: &HashMap<String, Term>) -> Term {
    match term {
        Term::QualIdentifier(identifier) => replacements
            .get(&identifier.get_name())
            .cloned()
            .unwrap_or_else(|| term.clone()),
        Term::Application {
            qual_identifier,
            arguments,
        } => Term::Application {
            qual_identifier: qual_identifier.clone(),
            arguments: arguments
                .iter()
                .map(|argument| replace_terms(argument, replacements))
                .collect(),
        },
        Term::Let { var_bindings, term } => Term::Let {
            var_bindings: var_bindings
                .iter()
                .map(|(symbol, binding)| (symbol.clone(), replace_terms(binding, replacements)))
                .collect(),
            term: Box::new(replace_terms(term, replacements)),
        },
        Term::Lambda { vars, term } => Term::Lambda {
            vars: vars.clone(),
            term: Box::new(replace_terms(term, replacements)),
        },
        Term::Forall { vars, term } => Term::Forall {
            vars: vars.clone(),
            term: Box::new(replace_terms(term, replacements)),
        },
        Term::Exists { vars, term } => Term::Exists {
            vars: vars.clone(),
            term: Box::new(replace_terms(term, replacements)),
        },
        Term::Match { term, cases } => Term::Match {
            term: Box::new(replace_terms(term, replacements)),
            cases: cases
                .iter()
                .map(|(symbols, case)| (symbols.clone(), replace_terms(case, replacements)))
                .collect(),
        },
        Term::Attributes { term, attributes } => Term::Attributes {
            term: Box::new(replace_terms(term, replacements)),
            attributes: attributes.clone(),
        },
        Term::Constant(_) => term.clone(),
    }
}

fn collect_read_indices(term: &Term, indices: &mut HashMap<String, HashSet<Term>>) {
    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            let name = qual_identifier.get_name();
            if name.starts_with("Read_") && arguments.len() == 2 {
                indices
                    .entry(name)
                    .or_default()
                    .insert(arguments[1].clone());
            }
            for argument in arguments {
                collect_read_indices(argument, indices);
            }
        }
        Term::Let { var_bindings, term } => {
            for (_, binding) in var_bindings {
                collect_read_indices(binding, indices);
            }
            collect_read_indices(term, indices);
        }
        // Reads beneath a binder have no ground index suitable for model
        // evaluation. Quantified rules handle these terms separately.
        Term::Lambda { .. } | Term::Forall { .. } | Term::Exists { .. } => {}
        Term::Attributes { term, .. } => collect_read_indices(term, indices),
        Term::Match { term, .. } => {
            collect_read_indices(term, indices);
        }
        Term::Constant(_) | Term::QualIdentifier(_) => {}
    }
}

fn collect_guarded_writes(term: &Term, guard: Option<Term>, writes: &mut Vec<GuardedWrite>) {
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        return;
    };

    match (qual_identifier.get_name().as_str(), arguments.as_slice()) {
        ("and", arguments) => {
            for argument in arguments {
                collect_guarded_writes(argument, guard.clone(), writes);
            }
        }
        ("=>", [antecedent, consequent]) => {
            let guard = Some(match guard {
                Some(outer) => application("and", vec![outer, antecedent.clone()]),
                None => antecedent.clone(),
            });
            collect_guarded_writes(consequent, guard, writes);
        }
        ("=", [left, right]) => {
            if let Some(write) = guarded_write(left, right, guard.clone()) {
                writes.push(write);
            }
            if let Some(write) = guarded_write(right, left, guard) {
                writes.push(write);
            }
        }
        _ => {}
    }
}

fn guarded_write(write: &Term, target: &Term, guard: Option<Term>) -> Option<GuardedWrite> {
    let Term::Application {
        qual_identifier,
        arguments,
    } = write
    else {
        return None;
    };
    let suffix = qual_identifier
        .get_name()
        .strip_prefix("Write_")?
        .to_string();
    let [base, index, value] = arguments.as_slice() else {
        return None;
    };
    Some(GuardedWrite {
        guard,
        read_name: format!("Read_{suffix}"),
        base: base.clone(),
        index: index.clone(),
        value: value.clone(),
        target: target.clone(),
    })
}

fn read(name: &str, array: Term, index: Term) -> Term {
    application(name, vec![array, index])
}

fn equals(left: Term, right: Term) -> Term {
    application("=", vec![left, right])
}

fn with_guard(guard: Option<Term>, consequence: Term) -> Term {
    match guard {
        Some(guard) => application("=>", vec![guard, consequence]),
        None => consequence,
    }
}

fn application(name: &str, arguments: Vec<Term>) -> Term {
    Term::Application {
        qual_identifier: QualIdentifier::simple(name),
        arguments,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn materializes_guarded_direct_and_property_read_updates() {
        let transition: Term = "(and (=> active (= (Write_Int_Int a i v) a_next)) (= n n_next))"
            .parse()
            .unwrap();
        let property: Term = "(= (Read_Int_Int a Z) 0)".parse().unwrap();

        assert_eq!(
            guarded_read_updates(&transition, &property, &HashMap::new())
                .into_iter()
                .map(|term| term.to_string())
                .collect::<Vec<_>>(),
            vec![
                "(=> active (= (Read_Int_Int a_next Z) (ite (= Z i) v (Read_Int_Int a Z))))",
                "(=> active (= (Read_Int_Int a_next i) v))",
            ]
        );
    }

    #[test]
    fn bound_read_indices_do_not_become_ground_lazy_schemas() {
        let transition: Term = "(and
            (=> active (= (Write_Int_Int a i v) a_next))
            (forall ((J Int)) (= (Read_Int_Int a J) 0)))"
            .parse()
            .unwrap();
        let property: Term = "(forall ((I Int)) (= (Read_Int_Int a I) 0))"
            .parse()
            .unwrap();

        let updates = guarded_read_updates(&transition, &property, &HashMap::new());

        assert_eq!(updates.len(), 1);
        assert_eq!(
            updates[0].to_string(),
            "(=> active (= (Read_Int_Int a_next i) v))"
        );
    }

    #[test]
    fn preserves_nested_action_guards() {
        let transition: Term = "(=> outer (=> inner (= a_next (Write_Int_Int a i v))))"
            .parse()
            .unwrap();
        let property: Term = "true".parse().unwrap();

        assert_eq!(
            guarded_read_updates(&transition, &property, &HashMap::new())[0].to_string(),
            "(=> (and outer inner) (= (Read_Int_Int a_next i) v))"
        );
    }

    #[test]
    fn shifts_tracked_indices_and_resolves_next_state_assignments() {
        let transition: Term = "(and
            (=> active (= (Write_Int_Int a i v) a_next))
            (=> active (= (+ i 1) i_next))
            (= Z Z_next)
            (= (Read_Int_Int a (- i 1)) old))"
            .parse()
            .unwrap();
        let property: Term = "(= (Read_Int_Int a Z) 0)".parse().unwrap();
        let current_to_next = HashMap::from([
            ("i".to_string(), "i_next".to_string()),
            ("Z".to_string(), "Z_next".to_string()),
        ]);

        let updates = guarded_read_updates(&transition, &property, &current_to_next)
            .into_iter()
            .map(|term| term.to_string())
            .collect::<HashSet<_>>();
        assert!(updates.contains(
            "(=> active (= (Read_Int_Int a_next Z) (ite (= Z i) v (Read_Int_Int a Z))))"
        ));
        assert!(updates.contains(
            "(=> active (= (Read_Int_Int a_next (- i_next 1)) (ite (= (- (+ i 1) 1) i) v (Read_Int_Int a (- (+ i 1) 1)))))"
        ));
    }

    #[test]
    fn distinguishes_constant_coefficients_from_nonlinear_products() {
        let linear: Term = "(* (Read_Int_Int a i) (- 1))".parse().unwrap();
        let nonlinear: Term = "(* (- i 1) (+ i 1))".parse().unwrap();

        assert!(!contains_genuinely_nonlinear_arithmetic(&linear));
        assert!(contains_genuinely_nonlinear_arithmetic(&nonlinear));
    }

    #[test]
    fn eager_read_composites_require_a_self_update() {
        let self_update: Term = "(+ (Read_Int_Int a i) (Read_Int_Int a j))".parse().unwrap();
        let cross_array: Term = "(- (Read_Int_Int a i) (Read_Int_Int b i))".parse().unwrap();
        let a: Term = "a".parse().unwrap();
        let c: Term = "c".parse().unwrap();

        assert!(is_small_self_read_composite(
            &self_update,
            "Read_Int_Int",
            &a
        ));
        assert!(!is_small_self_read_composite(
            &cross_array,
            "Read_Int_Int",
            &c
        ));
    }

    #[test]
    fn conservative_plan_omits_nonlinear_write_consequences() {
        let transition: Term = "(=> active (= (Write_Int_Int a i (* i i)) a_next))"
            .parse()
            .unwrap();
        let property: Term = "(= (Read_Int_Int a Z) 0)".parse().unwrap();

        let plan = guarded_read_update_plan(&transition, &property, &HashMap::new(), true);

        assert_eq!(plan.writes_detected, 1);
        assert_eq!(plan.writes_rejected_nonlinear, 1);
        assert!(plan.updates.is_empty());
    }

    #[test]
    fn conservative_plan_keeps_direct_consequences_for_additive_read_updates() {
        let transition: Term = "(and
            (= (Write_Int_Int a i i) a_mid)
            (= (Write_Int_Int a_mid i (+ (Read_Int_Int a_mid i) j)) a_next))"
            .parse()
            .unwrap();
        let property: Term = "(= (Read_Int_Int a Z) 0)".parse().unwrap();

        let plan = guarded_read_update_plan(&transition, &property, &HashMap::new(), true);
        let updates = plan
            .updates
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        let eager_updates = plan
            .eager_updates
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();

        assert_eq!(plan.writes_detected, 2);
        assert_eq!(plan.writes_rejected_expensive, 1);
        assert_eq!(plan.eager_read_composite_writes, 1);
        assert_eq!(updates.len(), 2);
        assert_eq!(eager_updates.len(), 2);
        assert!(eager_updates.iter().any(|update| {
            update == "(= (Read_Int_Int a_next i) (+ (Read_Int_Int a_mid i) j))"
        }));
        assert!(eager_updates.iter().any(|update| {
            update.contains("(ite ") && update.contains("(+ (Read_Int_Int a_mid i) j)")
        }));
    }

    #[test]
    fn conservative_plan_accepts_small_scalar_affine_write_values() {
        let transition: Term = "(=> active (= (Write_Int_Int a i (+ i 1)) a_next))"
            .parse()
            .unwrap();
        let property: Term = "(= (Read_Int_Int a Z) 0)".parse().unwrap();

        let plan = guarded_read_update_plan(&transition, &property, &HashMap::new(), true);

        assert_eq!(plan.writes_detected, 1);
        assert_eq!(plan.writes_rejected_expensive, 0);
        assert_eq!(plan.updates.len(), 2);
    }
    #[test]
    fn every_generated_consequence_is_entailed_by_concrete_array_theory() {
        let declarations = "
            (declare-const a (Array Int Int))
            (declare-const a_next (Array Int Int))
            (declare-const active Bool) (declare-const outer Bool)
            (declare-const i Int) (declare-const i_next Int)
            (declare-const j Int) (declare-const v Int) (declare-const old Int)";
        let transitions = [
            "(=> active (= a_next (Write_Int_Int a i v)))",
            "(=> outer (=> active (= a_next (Write_Int_Int a i v))))",
            "(and (=> active (= a_next (Write_Int_Int a i v))) (=> active (= i_next (+ i 1))) (= (Read_Int_Int a (- i 1)) old))",
            "(and (=> active (= a_next (Write_Int_Int a i v))) (=> outer (= i_next (+ i 1))) (= (Read_Int_Int a i) old))",
            "(=> active (= a_next (Write_Int_Int (Write_Int_Int a j 2) i v)))",
        ];
        let property = "(= (Read_Int_Int a j) 0)".parse().unwrap();
        let names = HashMap::from([("i".into(), "i_next".into())]);
        let concrete = |text: String| {
            text.replace("Read_Int_Int", "select")
                .replace("Write_Int_Int", "store")
        };
        for transition in transitions {
            let term = transition.parse().unwrap();
            let updates = guarded_read_updates(&term, &property, &names);
            assert!(!updates.is_empty());
            for update in updates {
                let solver = z3::Solver::new();
                solver.from_string(format!(
                    "{declarations} (assert {}) (assert (not {}))",
                    concrete(transition.to_string()),
                    concrete(update.to_string())
                ));
                assert_eq!(
                    solver.check(),
                    z3::SatResult::Unsat,
                    "{transition} does not entail {update}"
                );
            }
        }
    }

    #[test]
    fn boolean_writes_preserve_the_guard_even_when_it_is_false() {
        let transition: Term = "(=> active (= a_next (Write_Int_Bool a i true)))"
            .parse()
            .unwrap();
        let property = "(Read_Int_Bool a j)".parse().unwrap();
        let declarations =
            "(declare-const a (Array Int Bool)) (declare-const a_next (Array Int Bool))
            (declare-const active Bool) (declare-const i Int) (declare-const j Int)";
        for update in guarded_read_updates(&transition, &property, &HashMap::new()) {
            let solver = z3::Solver::new();
            solver.from_string(format!(
                "{declarations} (assert {}) (assert (not {}))",
                transition.to_string().replace("Write_Int_Bool", "store"),
                update.to_string().replace("Read_Int_Bool", "select")
            ));
            assert_eq!(solver.check(), z3::SatResult::Unsat);
        }
        // An inactive write must not constrain the next array at all.
        let solver = z3::Solver::new();
        solver.from_string(format!(
            "{declarations} (assert (not active))
            (assert {}) (assert (not (select a_next i)))",
            transition.to_string().replace("Write_Int_Bool", "store")
        ));
        assert_eq!(solver.check(), z3::SatResult::Sat);
    }
}
