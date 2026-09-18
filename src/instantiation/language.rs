//! Shared SMT term representation and conversion.
use egg::*;
use smt2parser::concrete::{Constant, Identifier, QualIdentifier, Symbol as SmtSymbol, Term};

define_language! {
    pub enum TermLanguage {
        Num(u64),
        // Parameterized array operations that include sort information as Symbol children
        // Format: "ConstArr" [index_sort_symbol, value_sort_symbol, value]
        "ConstArr" = ConstArrTyped([Id; 3]),
        // Format: "Write" [index_sort_symbol, value_sort_symbol, array, index, value]
        "Write" = WriteTyped([Id; 5]),
        // Format: "Read" [index_sort_symbol, value_sort_symbol, array, index]
        "Read" = ReadTyped([Id; 4]),
        "and" = And(Box<[Id]>),
        "not" = Not(Id),
        "or" = Or(Box<[Id]>),
        "=>" = Implies([Id; 2]),
        "=" = Eq([Id; 2]),
        ">=" = Geq([Id; 2]),
        ">" = Gt([Id; 2]),
        "<=" = Leq([Id; 2]),
        "<" = Lt([Id; 2]),
        "mod" = Mod([Id; 2]),
        "+" = Plus(Box<[Id]>),
        "-" = Negate(Box<[Id]>),
        "*" = Times(Box<[Id]>),
        "/" = Div([Id; 2]),
        "to_real" = ToReal(Id),
        "ite" = Ite([Id; 3]),
        Symbol(Symbol),
        // Keep existing node discriminants stable for deterministic array search.
        // Keep uninterpreted applications transparent to matching/extraction.
        // The first child is the (possibly qualified) function identifier.
        "$apply" = Apply(Box<[Id]>),
        // Internal typed domain membership used by input-binder searchers.
        "$domain" = Domain([Id; 2]),
        // Internal sort identity is disjoint from the SMT term namespace.
        // These leaves are constructed directly, never parsed as source terms.
        SortTag(Symbol),
    }
}

pub type TermExpr = egg::RecExpr<TermLanguage>;
pub type TermPattern = egg::PatternAst<TermLanguage>;

impl TermLanguage {
    pub fn sort_to_name(sort: &smt2parser::concrete::Sort) -> String {
        use smt2parser::concrete::{Identifier, Sort};
        match sort {
            Sort::Simple { identifier } => match identifier {
                Identifier::Simple { symbol } => symbol.0.clone(),
                Identifier::Indexed { symbol, indices } => {
                    // For indexed identifiers like (_ BitVec 32), format as "BitVec32"
                    let indices_str = indices
                        .iter()
                        .map(|idx| match idx {
                            smt2parser::visitors::Index::Numeral(n) => n.to_string(),
                            smt2parser::visitors::Index::Symbol(s) => s.0.clone(),
                        })
                        .collect::<Vec<_>>()
                        .join("_");
                    format!("{}{}", symbol.0, indices_str)
                }
            },
            Sort::Parameterized {
                identifier: _,
                parameters,
            } => parameters
                .iter()
                .map(Self::sort_to_name)
                .collect::<Vec<_>>()
                .join("_"),
        }
    }

    /// Format a typed array operation name (e.g., "Read_BitVec5_BitVec32" or "Read_Int_Array_Int_Int")
    pub fn format_array_op_name(op: &str, index_sort: &str, value_sort: &str) -> String {
        format!("{}_{}_{}", op, index_sort, value_sort)
    }

    pub fn extract_array_sorts(
        array_sort: &smt2parser::concrete::Sort,
    ) -> Option<(smt2parser::concrete::Sort, smt2parser::concrete::Sort)> {
        use smt2parser::concrete::{Identifier, Sort};
        match array_sort {
            Sort::Parameterized {
                identifier,
                parameters,
            } => {
                let is_array = match identifier {
                    Identifier::Simple { symbol } => symbol.0 == "Array",
                    Identifier::Indexed { symbol, .. } => symbol.0 == "Array",
                };
                if is_array && parameters.len() == 2 {
                    Some((parameters[0].clone(), parameters[1].clone()))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn read_typed(
        index_sort: &str,
        value_sort: &str,
        array: TermExpr,
        index: TermExpr,
    ) -> TermExpr {
        let mut expr = egg::RecExpr::default();
        let is = expr.add(TermLanguage::Symbol(index_sort.into()));
        let vs = expr.add(TermLanguage::Symbol(value_sort.into()));
        let a = expr.add(TermLanguage::Symbol("a".into()));
        let i = expr.add(TermLanguage::Symbol("i".into()));
        let read = expr.add(TermLanguage::ReadTyped([is, vs, a, i]));

        expr[read].join_recexprs(|id| {
            if id == a {
                array.clone()
            } else if id == i {
                index.clone()
            } else if id == is || id == vs {
                // Keep sort symbols as-is (they're not placeholders)
                RecExpr::from(vec![expr[id].clone()])
            } else {
                unreachable!()
            }
        })
    }

    pub fn write_typed(
        index_sort: &str,
        value_sort: &str,
        array: TermExpr,
        index: TermExpr,
        value: TermExpr,
    ) -> TermExpr {
        let mut expr = egg::RecExpr::default();
        let is = expr.add(TermLanguage::Symbol(index_sort.into()));
        let vs = expr.add(TermLanguage::Symbol(value_sort.into()));
        let a = expr.add(TermLanguage::Symbol("a".into()));
        let i = expr.add(TermLanguage::Symbol("i".into()));
        let v = expr.add(TermLanguage::Symbol("v".into()));
        let write = expr.add(TermLanguage::WriteTyped([is, vs, a, i, v]));

        expr[write].join_recexprs(|id| {
            if id == a {
                array.clone()
            } else if id == i {
                index.clone()
            } else if id == v {
                value.clone()
            } else if id == is || id == vs {
                // Keep sort symbols as-is (they're not placeholders)
                RecExpr::from(vec![expr[id].clone()])
            } else {
                unreachable!()
            }
        })
    }

    pub fn const_arr_typed(index_sort: &str, value_sort: &str, value: TermExpr) -> TermExpr {
        let mut expr = egg::RecExpr::default();
        let is = expr.add(TermLanguage::Symbol(index_sort.into()));
        let vs = expr.add(TermLanguage::Symbol(value_sort.into()));
        let v = expr.add(TermLanguage::Symbol("v".into()));
        let const_arr = expr.add(TermLanguage::ConstArrTyped([is, vs, v]));

        expr[const_arr].join_recexprs(|id| {
            if id == v {
                value.clone()
            } else if id == is || id == vs {
                // Keep sort symbols as-is (they're not placeholders)
                RecExpr::from(vec![expr[id].clone()])
            } else {
                unreachable!()
            }
        })
    }
}

/// Expermiental transformation from Term directly to egg::RecExpr,
/// so that we can skip using strings as an intermediate representation
pub fn translate_term(term: Term) -> Option<egg::RecExpr<TermLanguage>> {
    translate_term_with_array_types(term, &[])
}

/// Use declarations to disambiguate sort names containing underscores.
pub fn translate_term_with_array_types(
    term: Term,
    array_types: &[(String, String)],
) -> Option<egg::RecExpr<TermLanguage>> {
    fn inner(
        term: Term,
        expr: &mut egg::RecExpr<TermLanguage>,
        array_types: &[(String, String)],
    ) -> Option<egg::Id> {
        match term {
            Term::Constant(c) => match c {
                Constant::Numeral(value) => match value.clone().try_into() {
                    Ok(value) => Some(expr.add(TermLanguage::Num(value))),
                    Err(_) => Some(expr.add(TermLanguage::Symbol(value.to_string().into()))),
                },
                other => Some(expr.add(TermLanguage::Symbol(other.to_string().into()))),
            },
            Term::QualIdentifier(qi) => {
                let symbol = match qi {
                    QualIdentifier::Simple {
                        identifier: Identifier::Simple { symbol },
                    } => symbol.0,
                    other => other.to_string(),
                };
                Some(expr.add(TermLanguage::Symbol(symbol.into())))
            }
            Term::Application {
                qual_identifier,
                mut arguments,
            } => {
                let name = qual_identifier.get_name();

                // Check for parameterized array operations (e.g., "Read_BitVec5_BitVec32" or "Read_Int_Array_Int_Int")
                // Handle these before the match statement
                if let Some(rest) = name.strip_prefix("ConstArr_") {
                    // Parse "IndexSort_ValueSort" from the suffix - supports nested like "Int_Array_Int_Int"
                    let sorts = array_types
                        .iter()
                        .find(|(index, value)| rest == format!("{index}_{value}"))
                        .cloned()
                        .or_else(|| {
                            rest.split_once('_')
                                .map(|(index, value)| (index.to_string(), value.to_string()))
                        });
                    if let Some((index_sort, value_sort)) = sorts {
                        assert!(arguments.len() == 1);
                        let index_sort_id = expr.add(TermLanguage::Symbol(index_sort.into()));
                        let value_sort_id = expr.add(TermLanguage::Symbol(value_sort.into()));
                        let arg_id = inner(arguments.pop().unwrap(), expr, array_types)?;
                        return Some(expr.add(TermLanguage::ConstArrTyped([
                            index_sort_id,
                            value_sort_id,
                            arg_id,
                        ])));
                    }
                } else if let Some(rest) = name.strip_prefix("Write_") {
                    let sorts = array_types
                        .iter()
                        .find(|(index, value)| rest == format!("{index}_{value}"))
                        .cloned()
                        .or_else(|| {
                            rest.split_once('_')
                                .map(|(index, value)| (index.to_string(), value.to_string()))
                        });
                    if let Some((index_sort, value_sort)) = sorts {
                        assert!(arguments.len() == 3);
                        let index_sort_id = expr.add(TermLanguage::Symbol(index_sort.into()));
                        let value_sort_id = expr.add(TermLanguage::Symbol(value_sort.into()));
                        // args popped in reverse order
                        let val = inner(arguments.pop().unwrap(), expr, array_types)?;
                        let idx = inner(arguments.pop().unwrap(), expr, array_types)?;
                        let arr = inner(arguments.pop().unwrap(), expr, array_types)?;
                        return Some(expr.add(TermLanguage::WriteTyped([
                            index_sort_id,
                            value_sort_id,
                            arr,
                            idx,
                            val,
                        ])));
                    }
                } else if let Some(rest) = name.strip_prefix("Read_") {
                    let sorts = array_types
                        .iter()
                        .find(|(index, value)| rest == format!("{index}_{value}"))
                        .cloned()
                        .or_else(|| {
                            rest.split_once('_')
                                .map(|(index, value)| (index.to_string(), value.to_string()))
                        });
                    if let Some((index_sort, value_sort)) = sorts {
                        assert!(arguments.len() == 2);
                        let index_sort_id = expr.add(TermLanguage::Symbol(index_sort.into()));
                        let value_sort_id = expr.add(TermLanguage::Symbol(value_sort.into()));
                        // args popped in reverse order
                        let idx = inner(arguments.pop().unwrap(), expr, array_types)?;
                        let arr = inner(arguments.pop().unwrap(), expr, array_types)?;
                        return Some(expr.add(TermLanguage::ReadTyped([
                            index_sort_id,
                            value_sort_id,
                            arr,
                            idx,
                        ])));
                    }
                }

                // Original hardcoded patterns for backward compatibility (Int_Int arrays)
                match name.as_str() {
                    "and" => {
                        let arg_ids = arguments
                            .into_iter()
                            .map(|arg| inner(arg, expr, array_types))
                            .collect::<Option<_>>()?;
                        Some(expr.add(TermLanguage::And(arg_ids)))
                    }
                    "not" => {
                        assert!(arguments.len() == 1);
                        let arg_id = inner(arguments.pop().unwrap(), expr, array_types)?;
                        Some(expr.add(TermLanguage::Not(arg_id)))
                    }
                    "or" => {
                        let arg_ids = arguments
                            .into_iter()
                            .map(|arg| inner(arg, expr, array_types))
                            .collect::<Option<_>>()?;
                        Some(expr.add(TermLanguage::Or(arg_ids)))
                    }
                    "=>" => {
                        assert!(arguments.len() == 2);
                        // args popped in reverse order
                        let rhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        let lhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        Some(expr.add(TermLanguage::Implies([lhs, rhs])))
                    }
                    "=" => {
                        assert!(arguments.len() == 2);
                        // args popped in reverse order
                        let rhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        let lhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        Some(expr.add(TermLanguage::Eq([lhs, rhs])))
                    }
                    ">=" => {
                        assert!(arguments.len() == 2);
                        // args popped in reverse order
                        let rhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        let lhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        Some(expr.add(TermLanguage::Geq([lhs, rhs])))
                    }
                    ">" => {
                        assert!(arguments.len() == 2);
                        // args popped in reverse order
                        let rhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        let lhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        Some(expr.add(TermLanguage::Gt([lhs, rhs])))
                    }
                    "<=" => {
                        assert!(arguments.len() == 2);
                        // args popped in reverse order
                        let rhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        let lhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        Some(expr.add(TermLanguage::Leq([lhs, rhs])))
                    }
                    "<" => {
                        assert!(arguments.len() == 2);
                        // args popped in reverse order
                        let rhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        let lhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        Some(expr.add(TermLanguage::Lt([lhs, rhs])))
                    }
                    "mod" => {
                        assert!(arguments.len() == 2);
                        // args popped in reverse order
                        let rhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        let lhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        Some(expr.add(TermLanguage::Mod([lhs, rhs])))
                    }
                    "+" => {
                        let arg_ids = arguments
                            .into_iter()
                            .map(|arg| inner(arg, expr, array_types))
                            .collect::<Option<_>>()?;
                        Some(expr.add(TermLanguage::Plus(arg_ids)))
                    }
                    "-" => {
                        let arg_ids = arguments
                            .into_iter()
                            .map(|arg| inner(arg, expr, array_types))
                            .collect::<Option<_>>()?;
                        Some(expr.add(TermLanguage::Negate(arg_ids)))
                    }
                    "*" => {
                        let arg_ids = arguments
                            .into_iter()
                            .map(|arg| inner(arg, expr, array_types))
                            .collect::<Option<_>>()?;
                        Some(expr.add(TermLanguage::Times(arg_ids)))
                    }
                    "/" => {
                        assert!(arguments.len() == 2);
                        // args popped in reverse order
                        let rhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        let lhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        Some(expr.add(TermLanguage::Div([lhs, rhs])))
                    }
                    "to_real" => {
                        assert!(arguments.len() == 1);
                        let argument = inner(arguments.pop().unwrap(), expr, array_types)?;
                        Some(expr.add(TermLanguage::ToReal(argument)))
                    }
                    "ite" => {
                        assert!(arguments.len() == 3);
                        // args popped in reverse order
                        let else_term = inner(arguments.pop().unwrap(), expr, array_types)?;
                        let then_term = inner(arguments.pop().unwrap(), expr, array_types)?;
                        let condition = inner(arguments.pop().unwrap(), expr, array_types)?;
                        Some(expr.add(TermLanguage::Ite([condition, then_term, else_term])))
                    }
                    "bvcomp" => {
                        assert!(arguments.len() == 2);
                        let rhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        let lhs = inner(arguments.pop().unwrap(), expr, array_types)?;
                        let condition = expr.add(TermLanguage::Eq([lhs, rhs]));
                        let one = expr.add(TermLanguage::Symbol("#b1".into()));
                        let zero = expr.add(TermLanguage::Symbol("#b0".into()));
                        Some(expr.add(TermLanguage::Ite([condition, one, zero])))
                    }
                    _ => {
                        let head =
                            expr.add(TermLanguage::Symbol(qual_identifier.to_string().into()));
                        let mut children = vec![head];
                        for argument in arguments {
                            children.push(inner(argument, expr, array_types)?);
                        }
                        Some(expr.add(TermLanguage::Apply(children.into_boxed_slice())))
                    }
                }
            }
            Term::Lambda { .. } | Term::Forall { .. } => None,
            Term::Attributes { term, .. } => inner(*term, expr, array_types),
            opaque @ (Term::Let { .. } | Term::Exists { .. } | Term::Match { .. }) => {
                Some(expr.add(TermLanguage::Symbol(opaque.to_string().into())))
            }
        }
    }

    let mut expr = egg::RecExpr::default();
    inner(term, &mut expr, array_types)?;
    Some(expr)
}

fn is_simple_smt_symbol(symbol: &str) -> bool {
    fn is_non_digit_symbol_byte(byte: u8) -> bool {
        matches!(
            byte,
            b'a'..=b'z'
                | b'A'..=b'Z'
                | b'~'
                | b'!'
                | b'@'
                | b'$'
                | b'%'
                | b'^'
                | b'&'
                | b'*'
                | b'_'
                | b'-'
                | b'+'
                | b'='
                | b'<'
                | b'>'
                | b'.'
                | b'?'
                | b'/'
        )
    }

    let mut bytes = symbol.bytes();
    bytes.next().is_some_and(is_non_digit_symbol_byte)
        && bytes.all(|byte| byte.is_ascii_digit() || is_non_digit_symbol_byte(byte))
}

fn fast_symbol_term(symbol: &str) -> Option<Term> {
    if is_simple_smt_symbol(symbol) {
        return Some(Term::QualIdentifier(QualIdentifier::simple(symbol)));
    }

    let quoted = symbol
        .strip_prefix('|')
        .and_then(|symbol| symbol.strip_suffix('|'))?;
    (!quoted.bytes().any(|byte| matches!(byte, b'|' | b'\\')))
        .then(|| Term::QualIdentifier(QualIdentifier::simple(quoted)))
}

pub fn expr_to_term(expr: TermExpr) -> Term {
    fn inner(expr: &TermExpr, id: egg::Id) -> Term {
        match &expr[id] {
            TermLanguage::Apply(ids) => {
                let Term::QualIdentifier(qual_identifier) = inner(expr, ids[0]) else {
                    panic!("application head must be an SMT identifier");
                };
                Term::Application {
                    qual_identifier,
                    arguments: ids[1..].iter().map(|id| inner(expr, *id)).collect(),
                }
            }
            TermLanguage::Domain(_) | TermLanguage::SortTag(_) => {
                panic!("internal quantifier domain escaped grounding")
            }
            TermLanguage::Num(num) => Term::Constant(Constant::Numeral((*num).into())),
            TermLanguage::ConstArrTyped([index_sort, value_sort, x]) => {
                // Extract sort names from Symbol nodes
                let index_sort_name = match &expr[*index_sort] {
                    TermLanguage::Symbol(s) => s.as_str(),
                    _ => "Unknown",
                };
                let value_sort_name = match &expr[*value_sort] {
                    TermLanguage::Symbol(s) => s.as_str(),
                    _ => "Unknown",
                };
                let func_name = TermLanguage::format_array_op_name(
                    "ConstArr",
                    index_sort_name,
                    value_sort_name,
                );
                Term::Application {
                    qual_identifier: QualIdentifier::simple(func_name),
                    arguments: vec![inner(expr, *x)],
                }
            }
            TermLanguage::WriteTyped([index_sort, value_sort, arr, idx, val]) => {
                let index_sort_name = match &expr[*index_sort] {
                    TermLanguage::Symbol(s) => s.as_str(),
                    _ => "Unknown",
                };
                let value_sort_name = match &expr[*value_sort] {
                    TermLanguage::Symbol(s) => s.as_str(),
                    _ => "Unknown",
                };
                let func_name =
                    TermLanguage::format_array_op_name("Write", index_sort_name, value_sort_name);
                Term::Application {
                    qual_identifier: QualIdentifier::simple(func_name),
                    arguments: vec![inner(expr, *arr), inner(expr, *idx), inner(expr, *val)],
                }
            }
            TermLanguage::ReadTyped([index_sort, value_sort, arr, idx]) => {
                let index_sort_name = match &expr[*index_sort] {
                    TermLanguage::Symbol(s) => s.as_str(),
                    _ => "Unknown",
                };
                let value_sort_name = match &expr[*value_sort] {
                    TermLanguage::Symbol(s) => s.as_str(),
                    _ => "Unknown",
                };
                let func_name =
                    TermLanguage::format_array_op_name("Read", index_sort_name, value_sort_name);
                Term::Application {
                    qual_identifier: QualIdentifier::simple(func_name),
                    arguments: vec![inner(expr, *arr), inner(expr, *idx)],
                }
            }
            TermLanguage::And(ids) => Term::Application {
                qual_identifier: QualIdentifier::simple("and"),
                arguments: ids.iter().map(|id| inner(expr, *id)).collect(),
            },
            TermLanguage::Not(id) => Term::Application {
                qual_identifier: QualIdentifier::simple("not"),
                arguments: vec![inner(expr, *id)],
            },
            TermLanguage::Or(ids) => Term::Application {
                qual_identifier: QualIdentifier::simple("or"),
                arguments: ids.iter().map(|id| inner(expr, *id)).collect(),
            },
            TermLanguage::Implies([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("=>"),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            TermLanguage::Eq([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("="),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            TermLanguage::Geq([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple(">="),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            TermLanguage::Gt([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple(">"),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            TermLanguage::Leq([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("<="),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            TermLanguage::Lt([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("<"),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            TermLanguage::Mod([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("mod"),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            TermLanguage::Plus(ids) => Term::Application {
                qual_identifier: QualIdentifier::simple("+"),
                arguments: ids.iter().map(|id| inner(expr, *id)).collect(),
            },
            TermLanguage::Negate(ids) => Term::Application {
                qual_identifier: QualIdentifier::simple("-"),
                arguments: ids.iter().map(|id| inner(expr, *id)).collect(),
            },
            TermLanguage::Times(ids) => Term::Application {
                qual_identifier: QualIdentifier::simple("*"),
                arguments: ids.iter().map(|id| inner(expr, *id)).collect(),
            },
            TermLanguage::Div([lhs, rhs]) => Term::Application {
                qual_identifier: QualIdentifier::simple("/"),
                arguments: vec![inner(expr, *lhs), inner(expr, *rhs)],
            },
            TermLanguage::ToReal(argument) => Term::Application {
                qual_identifier: QualIdentifier::simple("to_real"),
                arguments: vec![inner(expr, *argument)],
            },
            TermLanguage::Ite([condition, then_term, else_term]) => Term::Application {
                qual_identifier: QualIdentifier::simple("ite"),
                arguments: vec![
                    inner(expr, *condition),
                    inner(expr, *then_term),
                    inner(expr, *else_term),
                ],
            },
            TermLanguage::Symbol(sym) => fast_symbol_term(sym.as_str()).unwrap_or_else(|| {
                sym.as_str().parse().unwrap_or_else(|_| {
                    SmtSymbol(sym.as_str().to_string())
                        .to_string()
                        .parse()
                        .expect("symbol preserved by the array e-graph must remain valid SMT-LIB")
                })
            }),
        }
    }

    inner(&expr, egg::Id::from(expr.as_ref().len() - 1))
}
