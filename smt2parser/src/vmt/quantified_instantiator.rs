use std::collections::BTreeMap;

use crate::{
    concrete::{Identifier, Sort, Symbol, SyntaxBuilder, Term},
    vmt::{variable::var_is_immutable, VARIABLE_FRAME_DELIMITER},
};

use super::{array_axiom_frame_num_getter::ArrayAxiomFrameNumGetter, variable::Variable};

#[derive(Clone)]
pub struct QuantifiedInstantiator {
    visitor: SyntaxBuilder,
    subst: BTreeMap<(String, usize), String>,
}

impl QuantifiedInstantiator {
    pub fn rewrite_no_prophecy(term: Term, variables: Vec<Variable>) -> Option<Term> {
        let frames = ArrayAxiomFrameNumGetter::new(term.clone(), variables.clone());
        if frames.needs_quantifier() {
            return None;
        }
        QuantifiedInstantiator::rewrite_quantified(term, variables)
    }

    pub fn rewrite_quantified(term: Term, variables: Vec<Variable>) -> Option<Term> {
        let frames = ArrayAxiomFrameNumGetter::new(term.clone(), variables);
        let (subst, quantified) = frames.to_substitution()?;
        let mut qi = Self {
            visitor: SyntaxBuilder,
            subst,
        };
        let rewritten = term.accept(&mut qi).unwrap();

        // TODO: keep track of types of variables
        if quantified.is_empty() {
            Some(rewritten)
        } else {
            Some(Term::Forall {
                vars: quantified
                    .into_iter()
                    .map(|var| {
                        (
                            Symbol(var.clone()),
                            Sort::Simple {
                                identifier: Identifier::Simple {
                                    // Only quantifying over Int types is guaranteed by ArrayAxiomFrameNumGetter.
                                    symbol: Symbol("Int".to_string()),
                                },
                            },
                        )
                    })
                    .collect(),
                term: Box::new(rewritten),
            })
        }
    }
}

impl crate::rewriter::Rewriter for QuantifiedInstantiator {
    type V = SyntaxBuilder;
    type Error = crate::concrete::Error;

    fn visitor(&mut self) -> &mut Self::V {
        &mut self.visitor
    }

    fn process_symbol(&mut self, s: Symbol) -> Result<Symbol, Self::Error> {
        match s.0.split_once(VARIABLE_FRAME_DELIMITER) {
            Some((var_name, _)) if var_is_immutable(var_name) => Ok(Symbol(var_name.to_string())),
            Some((var_name, frame)) => Ok(Symbol(
                self.subst[&(var_name.to_string(), frame.parse().unwrap())].clone(),
            )),
            None => Ok(s),
        }
    }
}
