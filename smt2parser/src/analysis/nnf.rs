use std::convert::TryInto;

use crate::concrete::{Identifier, QualIdentifier, Symbol, Term};
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Polarity {
    Positive,
    Negative,
}

impl Polarity {
    fn flipped(self) -> Self {
        match self {
            Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum NnfError {
    UnexpectedLet,
    UnexpectedMatch,
    ParseError(String),
}

pub fn to_nnf(term: Term) -> Result<Term, NnfError> {
    to_nnf_with_polarity(term, Polarity::Positive)
}

pub fn to_nnf_with_polarity(term: Term, polarity: Polarity) -> Result<Term, NnfError> {
    match term {
        Term::Constant(_) | Term::QualIdentifier(_) => wrap_atom(term, polarity),
        Term::Application {
            qual_identifier,
            arguments,
        } => rewrite_application(qual_identifier, arguments, polarity),
        Term::Let { .. } => Err(NnfError::UnexpectedLet),
        Term::Forall { vars, term } => {
            let inner = to_nnf_with_polarity(*term, polarity)?;
            let quantifier = match polarity {
                Polarity::Positive => Term::Forall {
                    vars,
                    term: Box::new(inner),
                },
                Polarity::Negative => Term::Exists {
                    vars,
                    term: Box::new(inner),
                },
            };
            Ok(quantifier)
        }
        Term::Exists { vars, term } => {
            let inner = to_nnf_with_polarity(*term, polarity)?;
            let quantifier = match polarity {
                Polarity::Positive => Term::Exists {
                    vars,
                    term: Box::new(inner),
                },
                Polarity::Negative => Term::Forall {
                    vars,
                    term: Box::new(inner),
                },
            };
            Ok(quantifier)
        }
        Term::Match { .. } => Err(NnfError::UnexpectedMatch),
        Term::Attributes { term, attributes } => Ok(Term::Attributes {
            term: Box::new(to_nnf_with_polarity(*term, polarity)?),
            attributes,
        }),
    }
}

fn rewrite_application(
    qual_identifier: QualIdentifier,
    arguments: Vec<Term>,
    polarity: Polarity,
) -> Result<Term, NnfError> {
    let Some(op) = application_symbol(&qual_identifier) else {
        return unknown_application(qual_identifier, arguments, polarity);
    };

    match op {
        "not" => {
            let [arg] = into_fixed_arity::<1>(arguments, op)?;
            to_nnf_with_polarity(arg, polarity.flipped())
        }
        "and" => {
            let out_op = match polarity {
                Polarity::Positive => "and",
                Polarity::Negative => "or",
            };
            rebuild_variadic_boolean(out_op, arguments, polarity)
        }
        "or" => {
            let out_op = match polarity {
                Polarity::Positive => "or",
                Polarity::Negative => "and",
            };
            rebuild_variadic_boolean(out_op, arguments, polarity)
        }
        "=>" => {
            let [lhs, rhs] = into_fixed_arity::<2>(arguments, op)?;
            match polarity {
                Polarity::Positive => build_boolean_application(
                    "or",
                    vec![
                        to_nnf_with_polarity(lhs, Polarity::Negative)?,
                        to_nnf_with_polarity(rhs, Polarity::Positive)?,
                    ],
                ),
                Polarity::Negative => build_boolean_application(
                    "and",
                    vec![
                        to_nnf_with_polarity(lhs, Polarity::Positive)?,
                        to_nnf_with_polarity(rhs, Polarity::Negative)?,
                    ],
                ),
            }
        }
        _ => unknown_application(qual_identifier, arguments, polarity),
    }
}

fn unknown_application(
    qual_identifier: QualIdentifier,
    arguments: Vec<Term>,
    polarity: Polarity,
) -> Result<Term, NnfError> {
    let atom = Term::Application {
        qual_identifier,
        arguments,
    };
    wrap_atom(atom, polarity)
}

fn wrap_atom(term: Term, polarity: Polarity) -> Result<Term, NnfError> {
    match polarity {
        Polarity::Positive => Ok(term),
        Polarity::Negative => build_boolean_application("not", vec![term]),
    }
}

fn rebuild_variadic_boolean(
    op: &str,
    arguments: Vec<Term>,
    polarity: Polarity,
) -> Result<Term, NnfError> {
    let rewritten = arguments
        .into_iter()
        .map(|arg| to_nnf_with_polarity(arg, polarity))
        .collect::<Result<Vec<_>, _>>()?;
    build_boolean_application(op, rewritten)
}

fn build_boolean_application(op: &str, arguments: Vec<Term>) -> Result<Term, NnfError> {
    Ok(Term::Application {
        qual_identifier: QualIdentifier::Simple {
            identifier: Identifier::Simple {
                symbol: Symbol(op.to_string()),
            },
        },
        arguments,
    })
}

fn application_symbol(qual_identifier: &QualIdentifier) -> Option<&str> {
    match qual_identifier {
        QualIdentifier::Simple { identifier } | QualIdentifier::Sorted { identifier, .. } => {
            match identifier {
                Identifier::Simple { symbol } => Some(symbol.0.as_str()),
                Identifier::Indexed { symbol, .. } => Some(symbol.0.as_str()),
            }
        }
    }
}

fn into_fixed_arity<const N: usize>(arguments: Vec<Term>, op: &str) -> Result<[Term; N], NnfError> {
    arguments
        .try_into()
        .map_err(|_| NnfError::ParseError(format!("operator `{op}` had unexpected arity")))
}

#[cfg(test)]
mod tests {
    use super::to_nnf;
    use crate::get_term_from_term_string;

    #[test]
    fn pushes_not_through_exists() {
        let term = get_term_from_term_string("(not (exists ((x Int)) (> x 0)))");
        let nnf = to_nnf(term).unwrap();
        assert_eq!(nnf.to_string(), "(forall ((x Int)) (not (> x 0)))");
    }

    #[test]
    fn leaves_non_boolean_atoms_negated() {
        let term = get_term_from_term_string("(not (= x y))");
        let nnf = to_nnf(term).unwrap();
        assert_eq!(nnf.to_string(), "(not (= x y))");
    }
}
