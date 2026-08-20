use std::collections::HashSet;

use crate::{
    analysis::nnf::to_nnf,
    concrete::{Command, QualIdentifier, Sort, Symbol, Term},
    let_extract::LetExtract,
};

pub(crate) struct HerbrandizedProperty {
    pub term: Term,
    pub declarations: Vec<Command>,
}

/// Replace the positive universal binders in a forall-only property with fresh
/// constants. Negating the returned property then produces the usual
/// quantifier-free Herbrand witness formula used by BMC.
///
/// The transformation is intentionally conservative. It accepts universals at
/// the root or below `and`/`or` after NNF conversion. Properties whose NNF has
/// existential binders or quantifiers in other Boolean positions are left
/// unchanged.
pub(crate) fn herbrandize_pure_universal_property(
    term: Term,
    reserved_names: impl IntoIterator<Item = String>,
) -> Option<HerbrandizedProperty> {
    let nnf = to_nnf(LetExtract::substitute(term)).ok()?;
    if !contains_forall(&nnf) || !has_supported_quantifier_positions(&nnf) {
        return None;
    }

    let mut herbrandizer = Herbrandizer {
        reserved_names: reserved_names.into_iter().collect(),
        ..Herbrandizer::default()
    };
    let term = herbrandizer.rewrite(nnf);
    Some(HerbrandizedProperty {
        term,
        declarations: herbrandizer.declarations,
    })
}

fn contains_forall(term: &Term) -> bool {
    match term {
        Term::Forall { .. } => true,
        Term::Application { arguments, .. } => arguments.iter().any(contains_forall),
        Term::Let { var_bindings, term } => {
            var_bindings.iter().any(|(_, term)| contains_forall(term)) || contains_forall(term)
        }
        Term::Lambda { term, .. } | Term::Exists { term, .. } | Term::Attributes { term, .. } => {
            contains_forall(term)
        }
        Term::Match { term, cases } => {
            contains_forall(term) || cases.iter().any(|(_, term)| contains_forall(term))
        }
        Term::Constant(_) | Term::QualIdentifier(_) => false,
    }
}

fn contains_quantifier(term: &Term) -> bool {
    match term {
        Term::Forall { .. } | Term::Exists { .. } => true,
        Term::Application { arguments, .. } => arguments.iter().any(contains_quantifier),
        Term::Let { var_bindings, term } => {
            var_bindings
                .iter()
                .any(|(_, binding)| contains_quantifier(binding))
                || contains_quantifier(term)
        }
        Term::Lambda { term, .. } | Term::Attributes { term, .. } => contains_quantifier(term),
        Term::Match { term, cases } => {
            contains_quantifier(term) || cases.iter().any(|(_, term)| contains_quantifier(term))
        }
        Term::Constant(_) | Term::QualIdentifier(_) => false,
    }
}

fn has_supported_quantifier_positions(term: &Term) -> bool {
    match term {
        Term::Forall { term, .. } => has_supported_quantifier_positions(term),
        Term::Exists { .. } => false,
        Term::Application {
            qual_identifier,
            arguments,
        } => {
            if !arguments.iter().any(contains_quantifier) {
                return true;
            }
            matches!(qual_identifier.get_name().as_str(), "and" | "or")
                && arguments.iter().all(has_supported_quantifier_positions)
        }
        Term::Attributes { term, .. } => has_supported_quantifier_positions(term),
        Term::Let { .. } => false,
        Term::Lambda { term, .. } => !contains_quantifier(term),
        Term::Match { term, cases } => {
            !contains_quantifier(term) && !cases.iter().any(|(_, case)| contains_quantifier(case))
        }
        Term::Constant(_) | Term::QualIdentifier(_) => true,
    }
}

#[derive(Default)]
struct Herbrandizer {
    next_id: usize,
    reserved_names: HashSet<String>,
    declarations: Vec<Command>,
}

impl Herbrandizer {
    fn fresh_constant(&mut self, sort: Sort) -> (Symbol, Term) {
        let name = loop {
            let name = format!("yardbird_herbrand_{}", self.next_id);
            self.next_id += 1;
            let next_name = format!("{name}.next");
            if !self.reserved_names.contains(&name) && !self.reserved_names.contains(&next_name) {
                self.reserved_names.insert(name.clone());
                self.reserved_names.insert(next_name);
                break name;
            }
        };
        let symbol = Symbol(name.clone());
        self.declarations.push(Command::DeclareFun {
            symbol: symbol.clone(),
            parameters: vec![],
            sort,
        });
        (symbol, Term::QualIdentifier(QualIdentifier::simple(name)))
    }

    fn rewrite(&mut self, term: Term) -> Term {
        match term {
            Term::Forall { vars, term } => {
                let bindings = vars
                    .into_iter()
                    .map(|(symbol, sort)| {
                        let (_, replacement) = self.fresh_constant(sort);
                        (symbol, replacement)
                    })
                    .collect();
                let substituted = LetExtract::substitute(Term::Let {
                    var_bindings: bindings,
                    term,
                });
                self.rewrite(substituted)
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => Term::Application {
                qual_identifier,
                arguments: arguments
                    .into_iter()
                    .map(|argument| self.rewrite(argument))
                    .collect(),
            },
            Term::Let { var_bindings, term } => Term::Let {
                var_bindings: var_bindings
                    .into_iter()
                    .map(|(symbol, binding)| (symbol, self.rewrite(binding)))
                    .collect(),
                term: Box::new(self.rewrite(*term)),
            },
            Term::Lambda { vars, term } => Term::Lambda {
                vars,
                term: Box::new(self.rewrite(*term)),
            },
            Term::Exists { .. } => unreachable!("existentials are rejected before rewriting"),
            Term::Match { term, cases } => Term::Match {
                term: Box::new(self.rewrite(*term)),
                cases: cases
                    .into_iter()
                    .map(|(symbols, case)| (symbols, self.rewrite(case)))
                    .collect(),
            },
            Term::Attributes { term, attributes } => Term::Attributes {
                term: Box::new(self.rewrite(*term)),
                attributes,
            },
            Term::Constant(_) | Term::QualIdentifier(_) => term,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn herbrandizes_a_forall_only_property() {
        let property: Term = "(forall ((C client) (D client)) (=> (not (= C D)) (p C D)))"
            .parse()
            .unwrap();

        let result = herbrandize_pure_universal_property(property, []).unwrap();

        assert_eq!(result.declarations.len(), 2);
        assert_eq!(
            result.term.to_string(),
            "(or (= yardbird_herbrand_0 yardbird_herbrand_1) (p yardbird_herbrand_0 yardbird_herbrand_1))"
        );
        assert_eq!(
            result.declarations[0].to_string(),
            "(declare-fun yardbird_herbrand_0 () client)"
        );
    }

    #[test]
    fn leaves_negative_universals_unchanged() {
        let property: Term = "(not (forall ((x Int)) (= x 0)))".parse().unwrap();

        assert!(herbrandize_pure_universal_property(property, []).is_none());
    }

    #[test]
    fn avoids_existing_generated_names() {
        let property: Term = "(forall ((x Int)) (= x 0))".parse().unwrap();

        let result =
            herbrandize_pure_universal_property(property, ["yardbird_herbrand_0".to_string()])
                .unwrap();

        assert!(result.term.to_string().contains("yardbird_herbrand_1"));
    }

    #[test]
    fn avoids_names_whose_next_symbol_already_exists() {
        let property: Term = "(forall ((x Int)) (= x 0))".parse().unwrap();

        let result =
            herbrandize_pure_universal_property(property, ["yardbird_herbrand_0.next".to_string()])
                .unwrap();

        assert!(result.term.to_string().contains("yardbird_herbrand_1"));
    }
}
