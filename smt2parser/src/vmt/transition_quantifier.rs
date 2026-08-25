use crate::concrete::{QualIdentifier, Sort, Symbol, Term};

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

    pub fn bound_variables(&self) -> &[(Symbol, Sort)] {
        match &self.quantified_formula {
            Term::Forall { vars, .. } => vars,
            _ => unreachable!("transition guards are discovered from forall terms"),
        }
    }

    pub fn body(&self) -> &Term {
        match &self.quantified_formula {
            Term::Forall { term, .. } => term,
            _ => unreachable!("transition guards are discovered from forall terms"),
        }
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

fn true_term() -> Term {
    Term::QualIdentifier(QualIdentifier::simple("true"))
}

fn abstract_guard_conjuncts(
    term: Term,
    action: &str,
    selected: &[TransitionGuard],
    removed: &mut Vec<TransitionGuard>,
) -> Term {
    if matches!(term, Term::Forall { .. }) {
        if let Some(guard) = selected
            .iter()
            .find(|guard| guard.action == action && guard.quantified_formula == term)
        {
            removed.push(guard.clone());
            return true_term();
        }
    }
    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } if application_name(&qual_identifier) == "and" => Term::Application {
            qual_identifier,
            arguments: arguments
                .into_iter()
                .map(|argument| abstract_guard_conjuncts(argument, action, selected, removed))
                .collect(),
        },
        other => other,
    }
}

fn abstract_actions(
    term: Term,
    selected: &[TransitionGuard],
    removed: &mut Vec<TransitionGuard>,
) -> Term {
    match term {
        Term::Application {
            qual_identifier,
            arguments,
        } if application_name(&qual_identifier) == "and" => Term::Application {
            qual_identifier,
            arguments: arguments
                .into_iter()
                .map(|argument| abstract_actions(argument, selected, removed))
                .collect(),
        },
        Term::Application {
            qual_identifier,
            mut arguments,
        } if application_name(&qual_identifier) == "=>" && arguments.len() == 2 => {
            let consequent = arguments.pop().unwrap();
            let antecedent = arguments.pop().unwrap();
            let consequent = action_name(&antecedent)
                .map(|action| {
                    abstract_guard_conjuncts(consequent.clone(), &action, selected, removed)
                })
                .unwrap_or(consequent);
            Term::Application {
                qual_identifier,
                arguments: vec![antecedent, consequent],
            }
        }
        Term::Attributes { term, attributes } => Term::Attributes {
            term: Box::new(abstract_actions(*term, selected, removed)),
            attributes,
        },
        other => other,
    }
}

pub(crate) fn abstract_transition_guards(
    transition: Term,
    selected: &[TransitionGuard],
) -> (Term, Vec<TransitionGuard>) {
    let mut removed = Vec::new();
    let transition = abstract_actions(transition, selected, &mut removed);
    (transition, removed)
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
        assert_eq!(guards[0].bound_variables().len(), 1);
        let (binder, _) = &guards[0].bound_variables()[0];
        assert_eq!(binder.0, "I:client");
        assert_eq!(
            guards[0].body().to_string(),
            "(not (Read_client_Bool homeSharerList |I:client|))"
        );
        assert_eq!(
            guards[0].quantified_formula().to_string(),
            "(forall ((|I:client| client)) (not (Read_client_Bool homeSharerList |I:client|)))"
        );
    }

    #[test]
    fn abstracts_only_selected_action_guards() {
        let transition: Term = "(and
            (=> grantExclusiveRule
                (and enabled
                    (forall ((|I:client| client))
                        (not (Read_client_Bool homeSharerList |I:client|)))))
            (forall ((ignored client)) (p ignored)))"
            .parse()
            .unwrap();
        let selected = discover_transition_guards(&transition);

        let (abstracted, removed) = abstract_transition_guards(transition, &selected);

        assert_eq!(removed, selected);
        assert_eq!(discover_transition_guards(&abstracted), vec![]);
        assert!(abstracted
            .to_string()
            .contains("(=> grantExclusiveRule (and enabled true))"));
        assert!(abstracted
            .to_string()
            .contains("(forall ((ignored client)) (p ignored))"));
    }
}
