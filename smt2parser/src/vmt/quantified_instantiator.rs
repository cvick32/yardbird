use std::{collections::BTreeMap, fmt::Display};

use crate::{
    concrete::{Identifier, Sort, Symbol, SyntaxBuilder, Term},
    vmt::{variable::var_is_immutable, VARIABLE_FRAME_DELIMITER},
};

use super::{array_axiom_frame_num_getter::ArrayAxiomFrameNumGetter, variable::Variable};

#[derive(PartialEq, Debug, Clone)]
pub struct Instance {
    instance: Term,
    all_substitution_variables_are_current: bool,
}
impl Display for Instance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.instance.to_string().as_str())
    }
}
impl Instance {
    pub fn get_term(&self) -> &Term {
        &self.instance
    }

    pub fn rewrite(&self, bmc_builder: &mut super::bmc::BMCBuilder) -> Term {
        self.instance.clone().accept(bmc_builder).unwrap()
    }

    pub fn additional_depth(&self) -> u8 {
        if self.all_substitution_variables_are_current {
            2
        } else {
            1
        }
    }
}

#[derive(Clone)]
pub struct QuantifiedInstantiator {
    visitor: SyntaxBuilder,
    subst: BTreeMap<(String, usize), String>,
}

impl QuantifiedInstantiator {
    pub fn rewrite_no_prophecy(term: Term, variables: Vec<Variable>) -> Option<Instance> {
        let frames = ArrayAxiomFrameNumGetter::new(term.clone(), variables.clone());
        if frames.needs_quantifier() {
            return None;
        }
        QuantifiedInstantiator::rewrite_quantified(term, variables)
    }

    pub fn rewrite_quantified(term: Term, variables: Vec<Variable>) -> Option<Instance> {
        let frames = ArrayAxiomFrameNumGetter::new(term.clone(), variables);
        let (subst, quantified, is_current) = frames.to_substitution()?;
        let mut qi = Self {
            visitor: SyntaxBuilder,
            subst,
        };
        let rewritten = term.accept(&mut qi).unwrap();

        let term = if quantified.is_empty() {
            rewritten
        } else {
            Term::Forall {
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
            }
        };
        Some(Instance {
            instance: term,
            all_substitution_variables_are_current: is_current,
        })
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
