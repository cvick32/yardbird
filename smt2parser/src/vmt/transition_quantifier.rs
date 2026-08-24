use crate::concrete::{QualIdentifier, Term};

/// Parser-level description of a positive universal guard in one transition
/// action. Yardbird adds refinement metadata after this syntax has been
/// recognized.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TransitionGuard {
    action: String,
    quantified_formula: Term,
}

impl TransitionGuard {
    pub fn action(&self) -> &str {
        &self.action
    }

    pub fn quantified_formula(&self) -> &Term {
        &self.quantified_formula
    }
}

fn application_name(identifier: &QualIdentifier) -> String {
    identifier.get_name()
}

fn action_name(term: &Term) -> Option<String> {
    match term {
        Term::QualIdentifier(identifier) => Some(application_name(identifier)),
        _ => None,
    }
}

fn collect_guard_formulas(term: &Term, guards: &mut Vec<Term>) {
    match term {
        Term::Forall { .. } => guards.push(term.clone()),
        Term::Application {
            qual_identifier,
            arguments,
        } if application_name(qual_identifier) == "and" => {
            for argument in arguments {
                collect_guard_formulas(argument, guards);
            }
        }
        _ => {}
    }
}

fn collect_actions(term: &Term, discovered: &mut Vec<TransitionGuard>) {
    let Term::Application {
        qual_identifier,
        arguments,
    } = term
    else {
        return;
    };
    match application_name(qual_identifier).as_str() {
        "and" => {
            for argument in arguments {
                collect_actions(argument, discovered);
            }
        }
        "=>" if arguments.len() == 2 => {
            let Some(action) = action_name(&arguments[0]) else {
                return;
            };
            let mut guards = Vec::new();
            collect_guard_formulas(&arguments[1], &mut guards);
            discovered.extend(
                guards
                    .into_iter()
                    .map(|quantified_formula| TransitionGuard {
                        action: action.clone(),
                        quantified_formula,
                    }),
            );
        }
        _ => {}
    }
}

/// Discover the German-style transition shape
/// `(=> action (and ... (forall (...) guard) ...))`.
///
/// Only conjunctions in action consequents are traversed. Universals in other
/// logical positions are deliberately outside this first supported fragment.
pub(crate) fn discover_transition_guards(transition: &Term) -> Vec<TransitionGuard> {
    let mut discovered = Vec::new();
    collect_actions(transition, &mut discovered);
    discovered
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn discovers_only_positive_foralls_in_action_conjunctions() {
        let transition: Term = "(and
            (=> grantExclusiveRule
                (and enabled
                    (forall ((|I:client| client))
                        (not (Read_client_Bool homeSharerList |I:client|)))))
            (forall ((ignored client)) (p ignored)))"
            .parse()
            .unwrap();

        let guards = discover_transition_guards(&transition);

        assert_eq!(guards.len(), 1);
        assert_eq!(guards[0].action(), "grantExclusiveRule");
        assert_eq!(
            guards[0].quantified_formula().to_string(),
            "(forall ((|I:client| client)) (not (Read_client_Bool homeSharerList |I:client|)))"
        );
    }
}
