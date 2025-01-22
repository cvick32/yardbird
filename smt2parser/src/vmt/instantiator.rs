use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::{
    concrete::{Identifier, Sort, Symbol, SyntaxBuilder, Term},
    vmt::{variable::var_is_immutable, VARIABLE_FRAME_DELIMITER},
};

use super::frame_num_getter::FrameNumGetter;

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
    pub fn rewrite(term: Term, frames: FrameNumGetter) -> Term {
        let min_frame_number = frames.min();
        let mut quantified = BTreeSet::new();
        println!("rewriting {term}");
        // println!("{frames:#?}");
        let subst = frames
            .frame_map
            .into_iter()
            .enumerate()
            .map(|(idx, (var, frame))| {
                if frame == min_frame_number || var_is_immutable(&var) {
                    ((var.clone(), frame), var)
                } else if frame == min_frame_number + 1 {
                    ((var.clone(), frame), format!("{var}_next"))
                } else {
                    let name = format!("PH{idx}");
                    quantified.insert(name.clone());
                    ((var, frame), name)
                }
            })
            .collect();

        let mut qi = Self {
            visitor: SyntaxBuilder,
            subst,
        };

        let rewritten = term.accept(&mut qi).unwrap();

        // TODO: keep track of types of variables
        if quantified.is_empty() {
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
                                    symbol: Symbol("Int".to_string()),
                                },
                            },
                        )
                    })
                    .collect(),
                term: Box::new(rewritten),
            }
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
            Some((var_name, _)) if var_is_immutable(var_name) => Ok(s),
            Some((var_name, frame)) => {
                if !self
                    .subst
                    .contains_key(&(var_name.to_string(), frame.parse().unwrap()))
                {
                    println!("searching for {var_name}@{frame} in {:#?}", self.subst);
                }
                Ok(Symbol(
                    self.subst[&(var_name.to_string(), frame.parse().unwrap())].clone(),
                ))
            }
            None => Ok(s),
        }
        // let symbol_split = s.0.split(VARIABLE_FRAME_DELIMITER).collect::<Vec<_>>();
        // if symbol_split.len() == 1 {
        //     // Symbol is not a variable
        //     Ok(s)
        // } else {
        //     let (variable_name, time_str) = (symbol_split[0], symbol_split[1]);
        //     if var_is_immutable(variable_name) {
        //         return Ok(Symbol(variable_name.to_string()));
        //     }
        //     let time: usize = time_str.parse().unwrap();
        //     if time == self.frames.min() {
        //         Ok(Symbol(variable_name.to_string()))
        //     } else if time == self.frames.max() {
        //         Ok(Symbol(
        //             self.current_to_next_variables
        //                 .get(variable_name)
        //                 .unwrap()
        //                 .to_string(),
        //         ))
        //     } else {
        //         todo!("Haven't implemented prophecy instantiation!")
        //     }
        // }
    }
}
