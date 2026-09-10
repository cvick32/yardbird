//! Recognition of the original single-index transition-guard fragment.
//! General quantifier instantiation lives in `quantifier_abstraction`.
use crate::{quantified_rule::TransitionGuardRule, theories::array::array_axioms::ArrayLanguage};
use smt2parser::concrete::Term;

pub fn supports_transition_guard(rule: &TransitionGuardRule) -> bool {
    let [(binder, sort)] = rule.bound_variables() else {
        return false;
    };
    is_supported_negative_read_guard(rule.body(), &binder.0, &ArrayLanguage::sort_to_name(sort))
}

fn is_supported_negative_read_guard(body: &Term, binder: &str, index_sort: &str) -> bool {
    let Term::Application {
        qual_identifier,
        arguments,
    } = body
    else {
        return false;
    };
    if qual_identifier.get_name() != "not" || arguments.len() != 1 {
        return false;
    }
    let Term::Application {
        qual_identifier,
        arguments,
    } = &arguments[0]
    else {
        return false;
    };
    let Some(array_sorts) = qual_identifier
        .get_name()
        .strip_prefix("Read_")
        .map(str::to_owned)
    else {
        return false;
    };
    let Some((read_index_sort, _)) = array_sorts.split_once('_') else {
        return false;
    };
    arguments.len() == 2
        && read_index_sort == index_sort
        && matches!(&arguments[1], Term::QualIdentifier(identifier) if identifier.get_name() == binder)
}
