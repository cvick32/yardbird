use std::collections::{BTreeMap, HashMap};

use crate::{
    concrete::{Identifier, Sort, Symbol, SyntaxBuilder, Term},
    vmt::{variable::var_is_immutable, VARIABLE_FRAME_DELIMITER},
};

use super::{
    array_axiom_frame_num_getter::ArrayAxiomFrameNumGetter, frame_num_getter::FrameNumGetter,
    variable::Variable,
};

#[derive(Clone)]
pub struct Instantiator {
    pub visitor: SyntaxBuilder,
    pub current_to_next_variables: HashMap<String, String>,
    pub frames: FrameNumGetter,
}

impl crate::rewriter::Rewriter for Instantiator {
    type V = SyntaxBuilder;
    type Error = crate::concrete::Error;

    fn visitor(&mut self) -> &mut Self::V {
        &mut self.visitor
    }

    fn process_symbol(&mut self, s: Symbol) -> Result<Symbol, Self::Error> {
        let symbol_split = s.0.split(VARIABLE_FRAME_DELIMITER).collect::<Vec<_>>();
        if symbol_split.len() == 1 {
            // Symbol is not a variable
            Ok(s)
        } else {
            let (variable_name, time_str) = (symbol_split[0], symbol_split[1]);
            if var_is_immutable(variable_name) {
                return Ok(Symbol(variable_name.to_string()));
            }
            let time: usize = time_str.parse().unwrap();
            if time == self.frames.min() {
                Ok(Symbol(variable_name.to_string()))
            } else if time == self.frames.max() {
                Ok(Symbol(
                    self.current_to_next_variables
                        .get(variable_name)
                        .unwrap()
                        .to_string(),
                ))
            } else {
                todo!("Haven't implemented prophecy instantiation!")
            }
        }
    }
}

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
