use std::{collections::BTreeMap, fmt::Display};

use crate::{
    concrete::{Identifier, Sort, Symbol, SyntaxBuilder, Term},
    vmt::{variable::var_is_immutable, VARIABLE_FRAME_DELIMITER},
};

use super::{
    array_axiom_frame_num_getter::{ArrayAxiomFrameNumGetter, VariableOffsetGetter},
    variable::Variable,
};

#[derive(PartialEq, Debug, Clone)]
pub struct Instance {
    instance: Term,
    all_substitution_variables_are_current: bool,
    width: u16,
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

    pub fn additional_depth(&self) -> u16 {
        if self.all_substitution_variables_are_current {
            2
        } else {
            1
        }
    }

    pub fn width(&self) -> u16 {
        self.width
    }
}

#[derive(Clone)]
pub struct QuantifiedInstantiator {
    visitor: SyntaxBuilder,
    subst: BTreeMap<(String, u64), String>,
}

impl QuantifiedInstantiator {
    pub fn rewrite_quantified(term: Term, variables: Vec<Variable>) -> Option<Instance> {
        let frames = ArrayAxiomFrameNumGetter::new(term.clone(), variables.clone());
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

        // Get variable offsets for distance calculation
        let offset_getter = VariableOffsetGetter::new(term.clone());

        Some(Instance {
            instance: term,
            all_substitution_variables_are_current: is_current,
            width: offset_getter.offset_span() as u16,
        })
    }
}

#[derive(Clone)]
pub struct UnquantifiedInstantiator {
    visitor: SyntaxBuilder,
    variable_offsets: VariableOffsetGetter,
}

impl UnquantifiedInstantiator {
    pub fn rewrite_unquantified(term: Term, _variables: Vec<Variable>) -> Option<Instance> {
        let offset_getter = VariableOffsetGetter::new(term.clone());
        let mut ui = Self {
            visitor: SyntaxBuilder,
            variable_offsets: offset_getter,
        };
        let rewritten = term.accept(&mut ui).unwrap();
        Some(Instance {
            instance: rewritten,
            all_substitution_variables_are_current: false,
            width: ui.variable_offsets.offset_span() as u16,
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

impl crate::rewriter::Rewriter for UnquantifiedInstantiator {
    type V = SyntaxBuilder;
    type Error = crate::concrete::Error;

    fn visitor(&mut self) -> &mut Self::V {
        &mut self.visitor
    }

    fn process_symbol(&mut self, s: Symbol) -> Result<Symbol, Self::Error> {
        match s.0.split_once(VARIABLE_FRAME_DELIMITER) {
            Some((var_name, _)) if var_is_immutable(var_name) => Ok(Symbol(var_name.to_string())),
            Some((var_name, frame)) => {
                let frame_num = frame.parse::<i64>().unwrap();
                let new_frame = frame_num - self.variable_offsets.min_offset();
                Ok(Symbol(format!("{var_name}+{new_frame}")))
            }
            None => Ok(s),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::concrete::{QualIdentifier, Term};

    /// Example demonstrating how VariableOffsetGetter and UnquantifiedInstantiator work
    #[test]
    fn test_variable_offset_analysis() {
        // Real instantiation from the terminal output:
        // (= (Read-Int-Int (Write-Int-Int b@0 i@0 (Read-Int-Int a@0 (- n@0 i@1))) i@0)
        //    (Read-Int-Int a@0 (- n@0 i@1)))

        // Create the term structure manually
        let write_term = Term::Application {
            qual_identifier: QualIdentifier::simple("Write-Int-Int"),
            arguments: vec![
                Term::QualIdentifier(QualIdentifier::simple("b@0")),
                Term::QualIdentifier(QualIdentifier::simple("i@0")),
                Term::Application {
                    qual_identifier: QualIdentifier::simple("Read-Int-Int"),
                    arguments: vec![
                        Term::QualIdentifier(QualIdentifier::simple("a@0")),
                        Term::Application {
                            qual_identifier: QualIdentifier::simple("-"),
                            arguments: vec![
                                Term::QualIdentifier(QualIdentifier::simple("n@0")),
                                Term::QualIdentifier(QualIdentifier::simple("i@1")),
                            ],
                        },
                    ],
                },
            ],
        };

        let read_write_term = Term::Application {
            qual_identifier: QualIdentifier::simple("Read-Int-Int"),
            arguments: vec![
                write_term,
                Term::QualIdentifier(QualIdentifier::simple("i@0")),
            ],
        };

        let read_a_term = Term::Application {
            qual_identifier: QualIdentifier::simple("Read-Int-Int"),
            arguments: vec![
                Term::QualIdentifier(QualIdentifier::simple("a@0")),
                Term::Application {
                    qual_identifier: QualIdentifier::simple("-"),
                    arguments: vec![
                        Term::QualIdentifier(QualIdentifier::simple("n@0")),
                        Term::QualIdentifier(QualIdentifier::simple("i@1")),
                    ],
                },
            ],
        };

        let example_term = Term::Application {
            qual_identifier: QualIdentifier::simple("="),
            arguments: vec![read_write_term, read_a_term],
        };

        // Test VariableOffsetGetter directly - it only needs the term to extract offsets
        let offset_getter = VariableOffsetGetter::new(example_term.clone());

        assert_eq!(offset_getter.min_offset(), 0);
        assert_eq!(offset_getter.max_offset(), 1);
        assert_eq!(offset_getter.offset_span(), 1);
    }

    #[test]
    fn test_variable_offset_large_span() {
        // Term: (= (Read-Int-Int (Write-Int-Int b@3 i@1 (Read-Int-Int a@2 (+ n@1 i@5))) i@5)
        //            (Read-Int-Int a@2 (+ n@1 i@5)))
        let write_term = Term::Application {
            qual_identifier: QualIdentifier::simple("Write-Int-Int"),
            arguments: vec![
                Term::QualIdentifier(QualIdentifier::simple("b@3")),
                Term::QualIdentifier(QualIdentifier::simple("i@1")),
                Term::Application {
                    qual_identifier: QualIdentifier::simple("Read-Int-Int"),
                    arguments: vec![
                        Term::QualIdentifier(QualIdentifier::simple("a@2")),
                        Term::Application {
                            qual_identifier: QualIdentifier::simple("+"),
                            arguments: vec![
                                Term::QualIdentifier(QualIdentifier::simple("n@1")),
                                Term::QualIdentifier(QualIdentifier::simple("i@5")),
                            ],
                        },
                    ],
                },
            ],
        };

        let read_write_term = Term::Application {
            qual_identifier: QualIdentifier::simple("Read-Int-Int"),
            arguments: vec![
                write_term,
                Term::QualIdentifier(QualIdentifier::simple("i@5")),
            ],
        };

        let read_a_term = Term::Application {
            qual_identifier: QualIdentifier::simple("Read-Int-Int"),
            arguments: vec![
                Term::QualIdentifier(QualIdentifier::simple("a@2")),
                Term::Application {
                    qual_identifier: QualIdentifier::simple("+"),
                    arguments: vec![
                        Term::QualIdentifier(QualIdentifier::simple("n@1")),
                        Term::QualIdentifier(QualIdentifier::simple("i@5")),
                    ],
                },
            ],
        };

        let example_term = Term::Application {
            qual_identifier: QualIdentifier::simple("="),
            arguments: vec![read_write_term, read_a_term],
        };

        let offset_getter = VariableOffsetGetter::new(example_term.clone());

        // Expected: b@3 (3), i@1 (1), i@5 (5), a@2 (2), n@1 (1)
        // min: 1, max: 5, span: 4, not uniform
        assert_eq!(offset_getter.min_offset(), 1);
        assert_eq!(offset_getter.max_offset(), 5);
        assert_eq!(offset_getter.offset_span(), 4);
    }

    #[test]
    fn test_unquantified_instantiator_rewriter() {
        // Same term as test_variable_offset_large_span:
        // (= (Read-Int-Int (Write-Int-Int b@3 i@1 (Read-Int-Int a@2 (+ n@1 i@5))) i@5)
        //    (Read-Int-Int a@2 (+ n@1 i@5)))
        let write_term = Term::Application {
            qual_identifier: QualIdentifier::simple("Write-Int-Int"),
            arguments: vec![
                Term::QualIdentifier(QualIdentifier::simple("b@3")),
                Term::QualIdentifier(QualIdentifier::simple("i@1")),
                Term::Application {
                    qual_identifier: QualIdentifier::simple("Read-Int-Int"),
                    arguments: vec![
                        Term::QualIdentifier(QualIdentifier::simple("a@2")),
                        Term::Application {
                            qual_identifier: QualIdentifier::simple("+"),
                            arguments: vec![
                                Term::QualIdentifier(QualIdentifier::simple("n@1")),
                                Term::QualIdentifier(QualIdentifier::simple("i@5")),
                            ],
                        },
                    ],
                },
            ],
        };

        let read_write_term = Term::Application {
            qual_identifier: QualIdentifier::simple("Read-Int-Int"),
            arguments: vec![
                write_term,
                Term::QualIdentifier(QualIdentifier::simple("i@5")),
            ],
        };

        let read_a_term = Term::Application {
            qual_identifier: QualIdentifier::simple("Read-Int-Int"),
            arguments: vec![
                Term::QualIdentifier(QualIdentifier::simple("a@2")),
                Term::Application {
                    qual_identifier: QualIdentifier::simple("+"),
                    arguments: vec![
                        Term::QualIdentifier(QualIdentifier::simple("n@1")),
                        Term::QualIdentifier(QualIdentifier::simple("i@5")),
                    ],
                },
            ],
        };

        let example_term = Term::Application {
            qual_identifier: QualIdentifier::simple("="),
            arguments: vec![read_write_term, read_a_term],
        };

        let empty_variables = vec![];

        // Test the UnquantifiedInstantiator rewriter
        if let Some(instance) =
            UnquantifiedInstantiator::rewrite_unquantified(example_term, empty_variables)
        {
            let rewritten_term = instance.get_term();

            // The rewriter should normalize offsets by subtracting min_offset (1)
            // So: b@3 -> b+2, i@1 -> i+0, a@2 -> a+1, n@1 -> n+0, i@5 -> i+4
            // Expected: (= (Read-Int-Int (Write-Int-Int b+2 i+0 (Read-Int-Int a+1 (+ n+0 i+4))) i+4) (Read-Int-Int a+1 (+ n+0 i+4)))

            // Convert to string to check the rewriting
            let rewritten_str = rewritten_term.to_string();

            // Check that the offsets have been normalized
            assert!(rewritten_str.contains("b+2")); // b@3 -> b+2 (3-1=2)
            assert!(rewritten_str.contains("i+0")); // i@1 -> i+0 (1-1=0)
            assert!(rewritten_str.contains("a+1")); // a@2 -> a+1 (2-1=1)
            assert!(rewritten_str.contains("n+0")); // n@1 -> n+0 (1-1=0)
            assert!(rewritten_str.contains("i+4")); // i@5 -> i+4 (5-1=4)

            // Check that no original frame annotations remain
            assert!(!rewritten_str.contains("@"));
        } else {
            panic!("Failed to create unquantified instance");
        }
    }

    #[test]
    fn test_width_calculation_real_instantiation() {
        // Real instantiation from the logs:
        // (=>
        //   (not (= i@0 i@1))
        //   (=
        //     (Read-Int-Int (Write-Int-Int b@1 i@1 (Read-Int-Int a@1 (- n@1 i@2))) i@0)
        //     (Read-Int-Int b@1 i@0)))

        let write_term = Term::Application {
            qual_identifier: QualIdentifier::simple("Write-Int-Int"),
            arguments: vec![
                Term::QualIdentifier(QualIdentifier::simple("b@1")),
                Term::QualIdentifier(QualIdentifier::simple("i@1")),
                Term::Application {
                    qual_identifier: QualIdentifier::simple("Read-Int-Int"),
                    arguments: vec![
                        Term::QualIdentifier(QualIdentifier::simple("a@1")),
                        Term::Application {
                            qual_identifier: QualIdentifier::simple("-"),
                            arguments: vec![
                                Term::QualIdentifier(QualIdentifier::simple("n@1")),
                                Term::QualIdentifier(QualIdentifier::simple("i@2")),
                            ],
                        },
                    ],
                },
            ],
        };

        let read_write_term = Term::Application {
            qual_identifier: QualIdentifier::simple("Read-Int-Int"),
            arguments: vec![
                write_term,
                Term::QualIdentifier(QualIdentifier::simple("i@0")),
            ],
        };

        let read_b_term = Term::Application {
            qual_identifier: QualIdentifier::simple("Read-Int-Int"),
            arguments: vec![
                Term::QualIdentifier(QualIdentifier::simple("b@1")),
                Term::QualIdentifier(QualIdentifier::simple("i@0")),
            ],
        };

        let equality_term = Term::Application {
            qual_identifier: QualIdentifier::simple("="),
            arguments: vec![read_write_term, read_b_term],
        };

        let not_equal_term = Term::Application {
            qual_identifier: QualIdentifier::simple("not"),
            arguments: vec![Term::Application {
                qual_identifier: QualIdentifier::simple("="),
                arguments: vec![
                    Term::QualIdentifier(QualIdentifier::simple("i@0")),
                    Term::QualIdentifier(QualIdentifier::simple("i@1")),
                ],
            }],
        };

        let implication_term = Term::Application {
            qual_identifier: QualIdentifier::simple("=>"),
            arguments: vec![not_equal_term, equality_term],
        };

        let empty_variables = vec![];

        // Test VariableOffsetGetter directly
        let offset_getter = VariableOffsetGetter::new(implication_term.clone());

        // Expected: i@0 (0), i@1 (1), b@1 (1), a@1 (1), n@1 (1), i@2 (2)
        // min: 0, max: 2, span: 2
        assert_eq!(offset_getter.min_offset(), 0);
        assert_eq!(offset_getter.max_offset(), 2);
        assert_eq!(offset_getter.offset_span(), 2);

        // Test UnquantifiedInstantiator
        if let Some(instance) =
            UnquantifiedInstantiator::rewrite_unquantified(implication_term, empty_variables)
        {
            assert_eq!(instance.width(), 2);
        } else {
            panic!("Failed to create unquantified instance");
        }
    }
}
