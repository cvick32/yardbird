//! Ground abstraction of recurrent nonlinear integer products.
//!
//! A product such as `i * c`, where `c` is transition-invariant, can be
//! represented by an immutable lookup array.  Constraining the reached
//! indices with `mul(0) = 0` and `mul(i) = c + mul(i - 1)` is an
//! over-approximation of integer multiplication and keeps the BMC query in
//! UF+linear arithmetic.

use std::collections::{HashMap, HashSet};

use smt2parser::{
    concrete::{
        AttributeValue, Command, Constant, FunctionDec, Identifier, Keyword, QualIdentifier, Sort,
        Symbol, Term,
    },
    vmt::{variable::Variable, VMTModel},
};

use super::stability::{certified_stable_states, exhaustive_next_assignments};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct ProductSpec {
    product: Term,
    counter: String,
    factor: String,
    quadratic: Option<QuadraticRecurrence>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Hash)]
struct QuadraticRecurrence {
    base: i64,
    delta_slope: i64,
    delta_intercept: i64,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct RecurrentProductReport {
    pub(super) stable_factor_candidates: usize,
    pub(super) products_abstracted: usize,
    pub(super) rejected_unproven_recurrence: usize,
}

/// Replace only products whose counter recurrence is syntactically proven by
/// the VMT initial state and transition relation.
pub(super) fn abstract_proven_recurrent_products(
    model: VMTModel,
    array_types: &[(String, String)],
) -> (VMTModel, RecurrentProductReport) {
    abstract_recurrent_products(model, array_types)
}

fn abstract_recurrent_products(
    mut model: VMTModel,
    array_types: &[(String, String)],
) -> (VMTModel, RecurrentProductReport) {
    if !array_types
        .iter()
        .any(|(index_sort, value_sort)| index_sort == "Int" && value_sort == "Int")
    {
        return (model, RecurrentProductReport::default());
    }

    let initial = model.get_initial_condition_for_yardbird();
    let transition = model.get_trans_condition_for_yardbird();
    let variables = model.get_state_variables();
    let current_to_next = variables
        .iter()
        .map(|variable| {
            (
                variable.get_current_variable_name().clone(),
                variable.get_next_variable_name().clone(),
            )
        })
        .collect::<HashMap<_, _>>();
    let next_names = current_to_next.values().cloned().collect::<HashSet<_>>();
    let integer_variables = variables
        .iter()
        .filter(|variable| variable.get_sort_name() == "Int")
        .map(|variable| variable.get_current_variable_name().clone())
        .collect::<HashSet<_>>();
    let stable_variables = certified_stable_states(&transition, &current_to_next);

    let mut stable_factor_specs = HashSet::new();
    collect_product_specs(
        &transition,
        &integer_variables,
        &stable_variables,
        &mut stable_factor_specs,
    );
    let stable_factor_candidates = stable_factor_specs.len();
    let recurrent_counters = integer_variables
        .iter()
        .filter(|counter| {
            !stable_variables.contains(*counter)
                && has_supported_initial_value(&initial, counter)
                && has_unit_recurrence(
                    &transition,
                    counter,
                    &current_to_next[counter.as_str()],
                    &next_names,
                )
        })
        .cloned()
        .collect::<HashSet<_>>();
    let mut specs = HashSet::new();
    collect_write_value_product_specs(
        &transition,
        &integer_variables,
        &stable_variables,
        &recurrent_counters,
        &mut specs,
    );
    let rejected_unproven_recurrence = stable_factor_candidates.saturating_sub(specs.len());
    if specs.is_empty() {
        return (
            model,
            RecurrentProductReport {
                stable_factor_candidates,
                products_abstracted: 0,
                rejected_unproven_recurrence,
            },
        );
    }

    let mut specs = specs.drain().collect::<Vec<_>>();
    specs.sort_by(|left, right| {
        (
            &left.counter,
            &left.factor,
            left.quadratic,
            left.product.to_string(),
        )
            .cmp(&(
                &right.counter,
                &right.factor,
                right.quadratic,
                right.product.to_string(),
            ))
    });
    let mut occupied_names = declared_term_symbols(model.as_commands());
    let table_names = specs
        .iter()
        .map(|spec| {
            let base = base_table_name(spec);
            let mut name = base.clone();
            let mut suffix = 0u32;
            while occupied_names.contains(&name) || occupied_names.contains(&format!("{name}_next"))
            {
                suffix += 1;
                name = format!("{base}_{suffix}");
            }
            occupied_names.insert(name.clone());
            occupied_names.insert(format!("{name}_next"));
            (spec.clone(), name)
        })
        .collect::<HashMap<_, _>>();
    let replacements = specs
        .iter()
        .map(|spec| {
            (
                spec.product.clone(),
                read(&table_names[spec], symbol(&spec.counter)),
            )
        })
        .collect::<HashMap<_, _>>();
    model.replace_transition_condition_for_yardbird(replace_subterms(&transition, &replacements));

    for spec in &specs {
        install_product_table(&mut model, spec, &table_names[spec]);
    }
    (
        model,
        RecurrentProductReport {
            stable_factor_candidates,
            products_abstracted: specs.len(),
            rejected_unproven_recurrence,
        },
    )
}

fn collect_write_value_product_specs(
    term: &Term,
    integer_variables: &HashSet<String>,
    stable_variables: &HashSet<String>,
    recurrent_counters: &HashSet<String>,
    specs: &mut HashSet<ProductSpec>,
) {
    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            if qual_identifier.get_name().starts_with("Write_") && arguments.len() == 3 {
                let mut value_specs = HashSet::new();
                collect_product_specs(
                    &arguments[2],
                    integer_variables,
                    stable_variables,
                    &mut value_specs,
                );
                specs.extend(
                    value_specs
                        .into_iter()
                        .filter(|spec| recurrent_counters.contains(&spec.counter)),
                );
                collect_quadratic_specs(&arguments[2], recurrent_counters, specs);
            }
            for argument in arguments {
                collect_write_value_product_specs(
                    argument,
                    integer_variables,
                    stable_variables,
                    recurrent_counters,
                    specs,
                );
            }
        }
        Term::Let { var_bindings, term } => {
            for (_, binding) in var_bindings {
                collect_write_value_product_specs(
                    binding,
                    integer_variables,
                    stable_variables,
                    recurrent_counters,
                    specs,
                );
            }
            collect_write_value_product_specs(
                term,
                integer_variables,
                stable_variables,
                recurrent_counters,
                specs,
            );
        }
        Term::Lambda { term, .. }
        | Term::Forall { term, .. }
        | Term::Exists { term, .. }
        | Term::Attributes { term, .. } => collect_write_value_product_specs(
            term,
            integer_variables,
            stable_variables,
            recurrent_counters,
            specs,
        ),
        Term::Match { term, cases } => {
            collect_write_value_product_specs(
                term,
                integer_variables,
                stable_variables,
                recurrent_counters,
                specs,
            );
            for (_, case) in cases {
                collect_write_value_product_specs(
                    case,
                    integer_variables,
                    stable_variables,
                    recurrent_counters,
                    specs,
                );
            }
        }
        Term::Constant(_) | Term::QualIdentifier(_) => {}
    }
}

fn collect_product_specs(
    term: &Term,
    integer_variables: &HashSet<String>,
    stable_variables: &HashSet<String>,
    specs: &mut HashSet<ProductSpec>,
) {
    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            if qual_identifier.get_name() == "*" && arguments.len() == 2 {
                let left = simple_symbol(&arguments[0]);
                let right = simple_symbol(&arguments[1]);
                let orientation = match (left, right) {
                    (Some(counter), Some(factor))
                        if integer_variables.contains(counter)
                            && integer_variables.contains(factor)
                            && stable_variables.contains(factor)
                            && counter != factor =>
                    {
                        Some((counter, factor))
                    }
                    (Some(factor), Some(counter))
                        if integer_variables.contains(counter)
                            && integer_variables.contains(factor)
                            && stable_variables.contains(factor)
                            && counter != factor =>
                    {
                        Some((counter, factor))
                    }
                    _ => None,
                };
                if let Some((counter, factor)) = orientation {
                    specs.insert(ProductSpec {
                        product: term.clone(),
                        counter: counter.to_string(),
                        factor: factor.to_string(),
                        quadratic: None,
                    });
                }
            }
            for argument in arguments {
                collect_product_specs(argument, integer_variables, stable_variables, specs);
            }
        }
        Term::Let { var_bindings, term } => {
            for (_, binding) in var_bindings {
                collect_product_specs(binding, integer_variables, stable_variables, specs);
            }
            collect_product_specs(term, integer_variables, stable_variables, specs);
        }
        Term::Lambda { term, .. }
        | Term::Forall { term, .. }
        | Term::Exists { term, .. }
        | Term::Attributes { term, .. } => {
            collect_product_specs(term, integer_variables, stable_variables, specs)
        }
        Term::Match { term, cases } => {
            collect_product_specs(term, integer_variables, stable_variables, specs);
            for (_, case) in cases {
                collect_product_specs(case, integer_variables, stable_variables, specs);
            }
        }
        Term::Constant(_) | Term::QualIdentifier(_) => {}
    }
}

fn collect_quadratic_specs(
    term: &Term,
    recurrent_counters: &HashSet<String>,
    specs: &mut HashSet<ProductSpec>,
) {
    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            if qual_identifier.get_name() == "*" && arguments.len() == 2 {
                for counter in recurrent_counters {
                    let Some((left_slope, left_intercept)) =
                        integer_affine_coefficients(&arguments[0], counter)
                    else {
                        continue;
                    };
                    let Some((right_slope, right_intercept)) =
                        integer_affine_coefficients(&arguments[1], counter)
                    else {
                        continue;
                    };
                    if left_slope != 0 && right_slope != 0 {
                        let quadratic = left_slope.checked_mul(right_slope);
                        let base = left_intercept.checked_mul(right_intercept);
                        let linear = left_slope.checked_mul(right_intercept).and_then(|left| {
                            left_intercept
                                .checked_mul(right_slope)
                                .and_then(|right| left.checked_add(right))
                        });
                        let Some((quadratic, base, linear)) = quadratic
                            .zip(base)
                            .zip(linear)
                            .map(|((quadratic, base), linear)| (quadratic, base, linear))
                        else {
                            continue;
                        };
                        let Some(delta_slope) = quadratic.checked_mul(2) else {
                            continue;
                        };
                        let Some(delta_intercept) = linear.checked_sub(quadratic) else {
                            continue;
                        };
                        specs.insert(ProductSpec {
                            product: term.clone(),
                            counter: counter.clone(),
                            factor: counter.clone(),
                            quadratic: Some(QuadraticRecurrence {
                                base,
                                delta_slope,
                                delta_intercept,
                            }),
                        });
                    }
                }
            }
            for argument in arguments {
                collect_quadratic_specs(argument, recurrent_counters, specs);
            }
        }
        Term::Let { var_bindings, term } => {
            for (_, binding) in var_bindings {
                collect_quadratic_specs(binding, recurrent_counters, specs);
            }
            collect_quadratic_specs(term, recurrent_counters, specs);
        }
        Term::Lambda { term, .. }
        | Term::Forall { term, .. }
        | Term::Exists { term, .. }
        | Term::Attributes { term, .. } => collect_quadratic_specs(term, recurrent_counters, specs),
        Term::Match { term, cases } => {
            collect_quadratic_specs(term, recurrent_counters, specs);
            for (_, case) in cases {
                collect_quadratic_specs(case, recurrent_counters, specs);
            }
        }
        Term::Constant(_) | Term::QualIdentifier(_) => {}
    }
}

fn integer_affine_coefficients(term: &Term, counter: &str) -> Option<(i64, i64)> {
    match term {
        Term::Constant(Constant::Numeral(value)) => {
            value.to_string().parse().ok().map(|value| (0, value))
        }
        Term::QualIdentifier(_) if simple_symbol(term) == Some(counter) => Some((1, 0)),
        Term::Application {
            qual_identifier,
            arguments,
        } if qual_identifier.get_name() == "+" && !arguments.is_empty() => {
            arguments.iter().try_fold((0i64, 0i64), |sum, argument| {
                let next = integer_affine_coefficients(argument, counter)?;
                Some((sum.0.checked_add(next.0)?, sum.1.checked_add(next.1)?))
            })
        }
        Term::Application {
            qual_identifier,
            arguments,
        } if qual_identifier.get_name() == "-" && !arguments.is_empty() => {
            let mut terms = arguments.iter();
            let first = integer_affine_coefficients(terms.next()?, counter)?;
            if arguments.len() == 1 {
                return Some((first.0.checked_neg()?, first.1.checked_neg()?));
            }
            terms.try_fold(first, |difference, argument| {
                let next = integer_affine_coefficients(argument, counter)?;
                Some((
                    difference.0.checked_sub(next.0)?,
                    difference.1.checked_sub(next.1)?,
                ))
            })
        }
        Term::Application {
            qual_identifier,
            arguments,
        } if qual_identifier.get_name() == "*" && arguments.len() == 2 => {
            if let Some(constant) = integer_constant(&arguments[0]) {
                let affine = integer_affine_coefficients(&arguments[1], counter)?;
                Some((
                    constant.checked_mul(affine.0)?,
                    constant.checked_mul(affine.1)?,
                ))
            } else if let Some(constant) = integer_constant(&arguments[1]) {
                let affine = integer_affine_coefficients(&arguments[0], counter)?;
                Some((
                    constant.checked_mul(affine.0)?,
                    constant.checked_mul(affine.1)?,
                ))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn integer_constant(term: &Term) -> Option<i64> {
    match term {
        Term::Constant(Constant::Numeral(value)) => value.to_string().parse().ok(),
        Term::Application {
            qual_identifier,
            arguments,
        } if qual_identifier.get_name() == "-" && arguments.len() == 1 => {
            integer_constant(&arguments[0])?.checked_neg()
        }
        _ => None,
    }
}

fn has_supported_initial_value(term: &Term, counter: &str) -> bool {
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        return false;
    };
    match (qual_identifier.get_name().as_str(), arguments.as_slice()) {
        ("and", arguments) => arguments
            .iter()
            .any(|argument| has_supported_initial_value(argument, counter)),
        ("=", [left, right]) => {
            (simple_symbol(left) == Some(counter) && is_zero_or_one(right))
                || (simple_symbol(right) == Some(counter) && is_zero_or_one(left))
        }
        _ => false,
    }
}

fn has_unit_recurrence(
    transition: &Term,
    counter: &str,
    next: &str,
    next_names: &HashSet<String>,
) -> bool {
    let Some(assignments) = exhaustive_next_assignments(transition, next, next_names) else {
        return false;
    };
    assignments.iter().any(|value| is_increment(value, counter))
        && assignments
            .iter()
            .all(|value| is_supported_counter_update(value, counter))
}

fn is_supported_counter_update(term: &Term, counter: &str) -> bool {
    simple_symbol(term) == Some(counter) || is_zero_or_one(term) || is_increment(term, counter)
}

fn is_increment(term: &Term, counter: &str) -> bool {
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        return false;
    };
    qual_identifier.get_name() == "+"
        && matches!(
            arguments.as_slice(),
            [left, right]
                if (simple_symbol(left) == Some(counter) && is_one(right))
                    || (is_one(left) && simple_symbol(right) == Some(counter))
        )
}

fn is_zero_or_one(term: &Term) -> bool {
    is_numeral(term, 0) || is_numeral(term, 1)
}

fn is_one(term: &Term) -> bool {
    is_numeral(term, 1)
}

fn is_numeral(term: &Term, expected: u64) -> bool {
    matches!(
        term,
        Term::Constant(Constant::Numeral(value)) if value.to_string() == expected.to_string()
    )
}

fn install_product_table(model: &mut VMTModel, spec: &ProductSpec, name: &str) {
    let name = name.to_string();
    let next_name = format!("{name}_next");
    let array_sort = simple_sort("Array_Int_Int");
    model.add_state_variable(Variable {
        current: Command::DeclareFun {
            symbol: Symbol(name.clone()),
            parameters: vec![],
            sort: array_sort.clone(),
        },
        next: Command::DeclareFun {
            symbol: Symbol(next_name.clone()),
            parameters: vec![],
            sort: array_sort,
        },
        relationship: Command::DefineFun {
            sig: FunctionDec {
                name: Symbol(format!(".{name}")),
                parameters: vec![],
                result: simple_sort("Array_Int_Int"),
            },
            term: Term::Attributes {
                term: Box::new(symbol(&name)),
                attributes: vec![(
                    Keyword("next".to_string()),
                    AttributeValue::Symbol(Symbol(next_name.clone())),
                )],
            },
        },
    });

    let zero = Term::Constant(Constant::Numeral(0u64.into()));
    let one = Term::Constant(Constant::Numeral(1u64.into()));
    let counter = symbol(&spec.counter);
    let (base_value, recurrence_delta) = if let Some(quadratic) = spec.quadratic {
        (
            integer_term(quadratic.base),
            affine_term(
                quadratic.delta_slope,
                counter.clone(),
                quadratic.delta_intercept,
            ),
        )
    } else {
        (zero.clone(), symbol(&spec.factor))
    };
    let base = equals(read(&name, zero.clone()), base_value);
    model.add_initial_constraint(base.clone());
    model.add_transition_constraint(base);
    model.add_transition_constraint(equals(symbol(&name), symbol(&next_name)));
    model.add_transition_constraint(application(
        "=>",
        vec![
            application(">", vec![counter.clone(), zero]),
            equals(
                read(&name, counter.clone()),
                application(
                    "+",
                    vec![
                        recurrence_delta,
                        read(&name, application("-", vec![counter, one])),
                    ],
                ),
            ),
        ],
    ));
}

fn declared_term_symbols(commands: impl IntoIterator<Item = Command>) -> HashSet<String> {
    let mut names = HashSet::new();
    for command in commands {
        match command {
            Command::DeclareConst { symbol, .. } | Command::DeclareFun { symbol, .. } => {
                names.insert(symbol.0);
            }
            Command::DefineFun { sig, .. } | Command::DefineFunRec { sig, .. } => {
                names.insert(sig.name.0);
            }
            Command::DefineFunsRec { funs } => {
                names.extend(funs.into_iter().map(|(sig, _)| sig.name.0));
            }
            _ => {}
        }
    }
    names
}

fn base_table_name(spec: &ProductSpec) -> String {
    if spec.quadratic.is_some() {
        format!("yb_quadratic_table_{}", sanitize(&spec.counter))
    } else {
        format!(
            "yb_mul_table_{}_{}",
            sanitize(&spec.counter),
            sanitize(&spec.factor)
        )
    }
}

fn affine_term(slope: i64, variable: Term, intercept: i64) -> Term {
    let variable_term = match slope {
        0 => None,
        1 => Some(variable),
        _ => Some(application("*", vec![integer_term(slope), variable])),
    };
    match (variable_term, intercept) {
        (None, constant) => integer_term(constant),
        (Some(term), 0) => term,
        (Some(term), constant) => application("+", vec![term, integer_term(constant)]),
    }
}

fn integer_term(value: i64) -> Term {
    if value < 0 {
        application(
            "-",
            vec![Term::Constant(Constant::Numeral(
                value.unsigned_abs().into(),
            ))],
        )
    } else {
        Term::Constant(Constant::Numeral((value as u64).into()))
    }
}

fn sanitize(name: &str) -> String {
    name.chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || character == '_' {
                character
            } else {
                '_'
            }
        })
        .collect()
}

fn replace_subterms(term: &Term, replacements: &HashMap<Term, Term>) -> Term {
    if let Some(replacement) = replacements.get(term) {
        return replacement.clone();
    }
    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } => Term::Application {
            qual_identifier: qual_identifier.clone(),
            arguments: arguments
                .iter()
                .map(|argument| replace_subterms(argument, replacements))
                .collect(),
        },
        Term::Let { var_bindings, term } => Term::Let {
            var_bindings: var_bindings
                .iter()
                .map(|(symbol, binding)| (symbol.clone(), replace_subterms(binding, replacements)))
                .collect(),
            term: Box::new(replace_subterms(term, replacements)),
        },
        Term::Lambda { vars, term } => Term::Lambda {
            vars: vars.clone(),
            term: Box::new(replace_subterms(term, replacements)),
        },
        Term::Forall { vars, term } => Term::Forall {
            vars: vars.clone(),
            term: Box::new(replace_subterms(term, replacements)),
        },
        Term::Exists { vars, term } => Term::Exists {
            vars: vars.clone(),
            term: Box::new(replace_subterms(term, replacements)),
        },
        Term::Match { term, cases } => Term::Match {
            term: Box::new(replace_subterms(term, replacements)),
            cases: cases
                .iter()
                .map(|(symbols, case)| (symbols.clone(), replace_subterms(case, replacements)))
                .collect(),
        },
        Term::Attributes { term, attributes } => Term::Attributes {
            term: Box::new(replace_subterms(term, replacements)),
            attributes: attributes.clone(),
        },
        Term::Constant(_) | Term::QualIdentifier(_) => term.clone(),
    }
}

fn simple_symbol(term: &Term) -> Option<&str> {
    let Term::QualIdentifier(QualIdentifier::Simple {
        identifier: Identifier::Simple { symbol },
    }) = term
    else {
        return None;
    };
    Some(&symbol.0)
}

fn simple_sort(name: &str) -> Sort {
    Sort::Simple {
        identifier: Identifier::Simple {
            symbol: Symbol(name.to_string()),
        },
    }
}

fn read(array: &str, index: Term) -> Term {
    application("Read_Int_Int", vec![symbol(array), index])
}

fn symbol(name: &str) -> Term {
    Term::QualIdentifier(QualIdentifier::simple(name))
}

fn equals(left: Term, right: Term) -> Term {
    application("=", vec![left, right])
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
    fn detects_products_with_an_unconditionally_stable_factor() {
        let transition: Term = "(and (= c c_next) (= x (* i c)))".parse().unwrap();
        let integers = HashSet::from(["i".to_string(), "c".to_string()]);
        let stable = HashSet::from(["c".to_string()]);
        let mut specs = HashSet::new();
        collect_product_specs(&transition, &integers, &stable, &mut specs);

        assert_eq!(specs.len(), 1);
        let spec = specs.into_iter().next().unwrap();
        assert_eq!(spec.counter, "i");
        assert_eq!(spec.factor, "c");
        assert!(spec.quadratic.is_none());
        assert!(certified_stable_states(
            &transition,
            &HashMap::from([("c".to_string(), "c_next".to_string())])
        )
        .contains("c"));
    }

    #[test]
    fn does_not_abstract_a_product_with_two_changing_operands() {
        let product: Term = "(* i j)".parse().unwrap();
        let integers = HashSet::from(["i".to_string(), "j".to_string()]);
        let mut specs = HashSet::new();
        collect_product_specs(&product, &integers, &HashSet::new(), &mut specs);
        assert!(specs.is_empty());
    }

    #[test]
    fn proves_initialized_unit_step_counter() {
        let initial: Term = "(and (= i 0) (> c 1))".parse().unwrap();
        let transition: Term = "(and
            (=> running (= (+ i 1) i_next))
            (=> reset_guard (= 0 i_next))
            (=> done (= i i_next))
            (or running reset_guard done))"
            .parse()
            .unwrap();

        assert!(has_supported_initial_value(&initial, "i"));
        assert!(has_unit_recurrence(
            &transition,
            "i",
            "i_next",
            &HashSet::from(["i_next".to_string()])
        ));
    }

    #[test]
    fn rejects_unit_update_with_an_uncovered_path() {
        let transition: Term = "(=> running (= (+ i 1) i_next))".parse().unwrap();

        assert!(!has_unit_recurrence(
            &transition,
            "i",
            "i_next",
            &HashSet::from(["i_next".to_string()])
        ));
    }

    #[test]
    fn rejects_counter_with_an_unsupported_jump() {
        let transition: Term = "(and (=> running (= (+ i 1) i_next)) (=> jump (= (+ i 2) i_next)))"
            .parse()
            .unwrap();

        assert!(!has_unit_recurrence(
            &transition,
            "i",
            "i_next",
            &HashSet::from(["i_next".to_string()])
        ));
    }

    #[test]
    fn conservative_collection_only_uses_write_values_and_proven_counters() {
        let transition: Term = "(and
            (= c c_next)
            (= outside (* i c))
            (= (Write_Int_Int a i (* i c)) a_next))"
            .parse()
            .unwrap();
        let integers = HashSet::from(["i".to_string(), "c".to_string()]);
        let stable = HashSet::from(["c".to_string()]);
        let recurrent = HashSet::from(["i".to_string()]);
        let mut specs = HashSet::new();

        collect_write_value_product_specs(&transition, &integers, &stable, &recurrent, &mut specs);

        assert_eq!(specs.len(), 1);
        assert_eq!(
            specs.into_iter().next().unwrap().product.to_string(),
            "(* i c)"
        );
    }

    #[test]
    fn abstracts_square_of_a_proven_unit_step_write_counter() {
        let model = VMTModel::from_path("examples/array/array_tiling_poly2.vmt")
            .unwrap()
            .abstract_array_theory_with_preprocessing(false)
            .0;
        let (rewritten, report) =
            abstract_proven_recurrent_products(model, &[("Int".into(), "Int".into())]);

        assert_eq!(report.products_abstracted, 1);
        assert!(!rewritten
            .get_trans_condition_for_yardbird()
            .to_string()
            .contains("(* i i)"));
    }

    #[test]
    fn abstracts_product_of_affine_terms_over_a_proven_counter() {
        let model = VMTModel::from_path("examples/array/array_tiling_poly4.vmt")
            .unwrap()
            .abstract_array_theory_with_preprocessing(false)
            .0;
        let (rewritten, report) =
            abstract_proven_recurrent_products(model, &[("Int".into(), "Int".into())]);

        assert_eq!(report.products_abstracted, 1);
        assert!(!rewritten
            .get_trans_condition_for_yardbird()
            .to_string()
            .contains("(* (+ i 1) (- i 1))"));
    }

    #[test]
    fn abstracts_a_product_with_an_exhaustively_guarded_stable_factor() {
        let model = VMTModel::from_path("examples/array/array_init_pair_symmetr4.vmt")
            .unwrap()
            .abstract_array_theory_with_preprocessing(false)
            .0;
        let (rewritten, report) =
            abstract_proven_recurrent_products(model, &[("Int".into(), "Int".into())]);

        assert_eq!(report.products_abstracted, 1);
        assert!(!rewritten
            .get_trans_condition_for_yardbird()
            .to_string()
            .contains("(* x i)"));
    }
}
