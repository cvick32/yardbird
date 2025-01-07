use std::collections::HashMap;

use num::BigUint;

use crate::{
    concrete::{
        self, AttributeValue, Command, Constant, FunctionDec, Identifier, Keyword, QualIdentifier,
        Sort, Symbol, SyntaxBuilder, Term,
    },
    rewriter::Rewriter,
    visitors::Smt2Visitor,
    vmt::variable::Variable,
};

const PREFIX: &str = "CONST";

#[derive(Clone, Debug, Default)]
pub struct ConstantAbstractor {
    visitor: SyntaxBuilder,
    depth: u8,
    next_id: usize,
    scope: HashMap<BigUint, usize>,
}

impl ConstantAbstractor {
    pub fn new(depth: u8) -> Self {
        Self {
            depth,
            ..Default::default()
        }
    }

    pub fn variables(&self) -> Vec<Variable> {
        (0..self.next_id)
            .map(|id| Variable {
                current: Command::DeclareFun {
                    symbol: Symbol(format!("{PREFIX}{id}")),
                    parameters: vec![],
                    sort: Sort::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol("Int".to_string()),
                        },
                    },
                },
                next: Command::DeclareFun {
                    symbol: Symbol(format!("{PREFIX}{id}_next")),
                    parameters: vec![],
                    sort: Sort::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol("Int".to_string()),
                        },
                    },
                },
                relationship: Command::DefineFun {
                    sig: FunctionDec {
                        name: Symbol(format!(".{PREFIX}{id}")),
                        parameters: vec![],
                        result: Sort::Simple {
                            identifier: Identifier::Simple {
                                symbol: Symbol("Int".to_string()),
                            },
                        },
                    },
                    term: Term::Attributes {
                        term: Box::new(Term::QualIdentifier(QualIdentifier::Simple {
                            identifier: Identifier::Simple {
                                symbol: Symbol(format!("{PREFIX}{id}")),
                            },
                        })),
                        attributes: vec![(
                            Keyword("next".to_string()),
                            AttributeValue::Symbol(Symbol(format!("{PREFIX}{id}_next"))),
                        )],
                    },
                },
            })
            .collect()
    }

    pub fn transition_properties(&self, transition: Term) -> Term {
        let terms = (0..self.next_id)
            .map(|id| Term::Application {
                qual_identifier: QualIdentifier::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol("=".to_string()),
                    },
                },
                arguments: vec![
                    Term::QualIdentifier(QualIdentifier::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol(format!("{PREFIX}{id}")),
                        },
                    }),
                    Term::QualIdentifier(QualIdentifier::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol(format!("{PREFIX}{id}_next")),
                        },
                    }),
                ],
            })
            .collect();

        let mut appender = AppendProperty::new(terms);
        transition.accept(&mut appender).unwrap()
    }

    pub fn invariant_properties(&self, invariant: Term) -> Term {
        let terms = (0..self.next_id)
            .map(|id| Term::Application {
                qual_identifier: QualIdentifier::Simple {
                    identifier: Identifier::Simple {
                        symbol: Symbol(">".to_string()),
                    },
                },
                arguments: vec![
                    Term::QualIdentifier(QualIdentifier::Simple {
                        identifier: Identifier::Simple {
                            symbol: Symbol(format!("{PREFIX}{id}")),
                        },
                    }),
                    Term::Constant(Constant::Numeral(BigUint::from(1u32))),
                ],
            })
            .collect();

        let mut appender = AppendProperty::new(terms);
        invariant.accept(&mut appender).unwrap()
    }

    fn construct_identifier(&self, id: usize) -> QualIdentifier {
        QualIdentifier::Simple {
            identifier: Identifier::Simple {
                symbol: Symbol(format!("{PREFIX}{id}")),
            },
        }
    }

    fn fresh_id(&mut self) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        id
    }
}

impl Rewriter for ConstantAbstractor {
    type V = SyntaxBuilder;
    type Error = concrete::Error;

    fn visitor(&mut self) -> &mut Self::V {
        &mut self.visitor
    }

    fn visit_constant(
        &mut self,
        constant: Constant,
    ) -> Result<<Self::V as Smt2Visitor>::Term, Self::Error> {
        match constant {
            Constant::Numeral(big_uint) if big_uint > self.depth.into() => {
                if let Some(id) = self.scope.get(&big_uint) {
                    Ok(Term::QualIdentifier(self.construct_identifier(*id)))
                } else {
                    let id = self.fresh_id();
                    self.scope.insert(big_uint, id);
                    Ok(Term::QualIdentifier(self.construct_identifier(id)))
                }
            }
            x => Ok(Term::Constant(x)),
        }
    }
}

/// Visitor that appends a boolean term to the first `and` that we come across.
struct AppendProperty {
    visitor: SyntaxBuilder,
    term: Vec<Term>,
}

impl AppendProperty {
    pub fn new(term: Vec<Term>) -> Self {
        Self {
            term,
            visitor: SyntaxBuilder,
        }
    }
}

impl Rewriter for AppendProperty {
    type V = SyntaxBuilder;
    type Error = concrete::Error;

    fn visitor(&mut self) -> &mut Self::V {
        &mut self.visitor
    }

    fn visit_application(
        &mut self,
        qual_identifier: <Self::V as Smt2Visitor>::QualIdentifier,
        mut arguments: Vec<<Self::V as Smt2Visitor>::Term>,
    ) -> Result<<Self::V as Smt2Visitor>::Term, Self::Error> {
        if !self.term.is_empty() && qual_identifier.get_name() == "and" {
            // this leaves `self.term` empty, so this will only run on the first
            // `and` that we encounter. The first and seems to be the deepest one.
            // I think that's fine
            arguments.append(&mut self.term);
        }

        Ok(Term::Application {
            qual_identifier,
            arguments,
        })
    }
}
