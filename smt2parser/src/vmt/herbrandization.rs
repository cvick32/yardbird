use std::collections::HashSet;

use crate::{
    analysis::nnf::to_nnf,
    concrete::{Command, QualIdentifier, Sort, Symbol, Term},
    let_extract::LetExtract,
};

pub(crate) struct HerbrandizedProperty {
    pub term: Term,
    pub declarations: Vec<Command>,
    pub bindings: Vec<(Symbol, Symbol)>,
}

/// Which universal binders a caller can expose as rigid BMC witnesses.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PropertyWitnessScope {
    /// The entire property must be in the supported universal fragment.
    PureUniversal,
    /// Leave subformulas beyond a positive universal/and/or path with the solver.
    OuterUniversals,
}

pub(crate) fn herbrandize_property(
    term: Term,
    reserved_names: impl IntoIterator<Item = String>,
    scope: PropertyWitnessScope,
) -> Option<HerbrandizedProperty> {
    let nnf = to_nnf(LetExtract::substitute(term)).ok()?;
    if scope == PropertyWitnessScope::PureUniversal && !has_supported_quantifier_positions(&nnf) {
        return None;
    }

    let mut herbrandizer = Herbrandizer {
        reserved_names: reserved_names.into_iter().collect(),
        ..Herbrandizer::default()
    };
    // A retained binder may itself be named yardbird_herbrand_N. Reserve those
    // names as well as global declarations before substituting below it.
    let syntax = nnf.to_string();
    if syntax.contains("yardbird_herbrand_") {
        herbrandizer
            .reserved_names
            .extend(
                crate::lexer::Lexer::new(syntax.as_bytes()).filter_map(|token| match token {
                    crate::parser::Token::Symbol(name)
                        if name.starts_with("yardbird_herbrand_") =>
                    {
                        Some(name)
                    }
                    _ => None,
                }),
            );
    }
    let term = herbrandizer.rewrite(nnf);
    (!herbrandizer.bindings.is_empty()).then_some(HerbrandizedProperty {
        term,
        declarations: herbrandizer.declarations,
        bindings: herbrandizer.bindings,
    })
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
    bindings: Vec<(Symbol, Symbol)>,
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
                        let (witness, replacement) = self.fresh_constant(sort);
                        self.bindings.push((symbol.clone(), witness));
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
            } if matches!(qual_identifier.get_name().as_str(), "and" | "or") => Term::Application {
                qual_identifier,
                arguments: arguments.into_iter().map(|arg| self.rewrite(arg)).collect(),
            },
            Term::Attributes { term, attributes } => Term::Attributes {
                term: Box::new(self.rewrite(*term)),
                attributes,
            },
            // An existential may bind variables on which deeper universals depend.
            // Under any opaque operator the polarity of its arguments is unknown.
            other => other,
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

        let result =
            herbrandize_property(property, [], PropertyWitnessScope::PureUniversal).unwrap();

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

        assert!(herbrandize_property(property, [], PropertyWitnessScope::PureUniversal).is_none());
    }

    #[test]
    fn residual_existential_keeps_its_scope_and_cannot_capture_the_witness() {
        let source: Term =
            "(forall ((x Int)) (exists ((yardbird_herbrand_0 Int)) (= x yardbird_herbrand_0)))"
                .parse()
                .unwrap();
        assert!(
            herbrandize_property(source.clone(), [], PropertyWitnessScope::PureUniversal).is_none()
        );
        let result =
            herbrandize_property(source, [], PropertyWitnessScope::OuterUniversals).unwrap();
        assert_eq!(
            result.term.to_string(),
            "(exists ((yardbird_herbrand_0 Int)) (= yardbird_herbrand_1 yardbird_herbrand_0))"
        );
        assert_eq!(result.bindings.len(), 1);
    }

    #[test]
    fn avoids_existing_generated_names() {
        let property: Term = "(forall ((x Int)) (= x 0))".parse().unwrap();

        let result = herbrandize_property(
            property,
            ["yardbird_herbrand_0".to_string()],
            PropertyWitnessScope::PureUniversal,
        )
        .unwrap();

        assert!(result.term.to_string().contains("yardbird_herbrand_1"));
    }

    #[test]
    fn avoids_names_whose_next_symbol_already_exists() {
        let property: Term = "(forall ((x Int)) (= x 0))".parse().unwrap();

        let result = herbrandize_property(
            property,
            ["yardbird_herbrand_0.next".to_string()],
            PropertyWitnessScope::PureUniversal,
        )
        .unwrap();

        assert!(result.term.to_string().contains("yardbird_herbrand_1"));
    }
}
