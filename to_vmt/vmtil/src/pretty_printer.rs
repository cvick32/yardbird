use pretty::RcDoc;

use crate::{
    vmtil::{BooleanExpr, Expr},
    Type,
};

pub type Doc<'a> = RcDoc<'a, ()>;

pub trait ToDoc {
    fn to_doc(&self) -> Doc;
}

impl ToDoc for Type {
    fn to_doc(&self) -> Doc {
        match self {
            Type::Int => Doc::text("Int"),
            Type::Bool => Doc::text("Bool"),
            Type::Array { index, value } => Doc::text("(")
                .append("Array")
                .append(Doc::space())
                .append(index.to_doc())
                .append(Doc::space())
                .append(value.to_doc())
                .append(")"),
        }
    }
}

impl ToDoc for Expr {
    fn to_doc(&self) -> Doc {
        match self {
            Expr::Store { array, index, expr } => Doc::text("(")
                .append("store")
                .append(Doc::line())
                .append(array)
                .append(Doc::line())
                .append(index)
                .append(Doc::line())
                .append(expr.to_doc())
                .append(")"),
            Expr::Select { array, index } => Doc::text("(")
                .append("select")
                .append(Doc::line())
                .append(array)
                .append(Doc::line())
                .append(index)
                .append(")"),
            Expr::Var(var) => Doc::text(var),
            Expr::Lit(lit) => Doc::text(lit),
            Expr::Boolean(boolean_expr) => boolean_expr.to_doc(),
            Expr::ArithBinop { op, lhs, rhs } => Doc::text("(")
                .append(op)
                .append(Doc::line())
                .append(lhs.to_doc())
                .append(Doc::line())
                .append(rhs.to_doc())
                .append(")"),
        }
    }
}

impl ToDoc for BooleanExpr {
    fn to_doc(&self) -> Doc {
        match self {
            BooleanExpr::Forall { quantified, expr } => Doc::text("(")
                .append("forall")
                .append(Doc::space())
                .append(quantified)
                .append(Doc::space())
                .append(".")
                .append(Doc::space())
                .append(expr.to_doc())
                .append(")"),
            BooleanExpr::Var(var) => Doc::text(var),
            BooleanExpr::Lit(lit) => Doc::text(lit),
            BooleanExpr::Binop { op, lhs, rhs } if op == "=>" => Doc::text("(")
                .append(op)
                .append(Doc::space().append(lhs.to_doc()))
                .append(Doc::hardline().append(rhs.to_doc()).nest(4).group())
                .append(")")
                .group(),
            BooleanExpr::Binop { op, lhs, rhs } => Doc::text("(")
                .append(op)
                .append(Doc::line())
                .append(lhs.to_doc())
                .append(Doc::line())
                .append(rhs.to_doc())
                .append(")")
                .group(),
            BooleanExpr::Conjunction(vec) if vec.is_empty() => Doc::text("true"),
            BooleanExpr::Conjunction(vec) => Doc::text("(")
                .append("and")
                .append(
                    Doc::line()
                        .append(Doc::intersperse(
                            vec.iter()
                                .filter(|ex| !matches!(ex, BooleanExpr::True))
                                .map(|ex| ex.to_doc()),
                            Doc::line(),
                        ))
                        .nest(2)
                        .group(),
                )
                .append(")"),
            BooleanExpr::Not(boolean_expr) => Doc::text("(")
                .append("not")
                .append(Doc::line())
                .append(boolean_expr.to_doc())
                .append(")")
                .group(),
            BooleanExpr::True => Doc::text("true"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum VmtCommands {
    DeclareFun {
        variable: String,
        // TODO: use something other than strings at some point
        arguments: Vec<Type>,
        output_type: Type,
    },
    DefineFun {
        variable: String,
        arguments: Vec<Type>,
        output_type: Type,
        definition: BooleanExpr,
        flags: Vec<(String, String)>,
    },
}

impl ToDoc for VmtCommands {
    fn to_doc(&self) -> Doc {
        match self {
            VmtCommands::DeclareFun {
                variable,
                arguments,
                output_type,
            } => Doc::text("(")
                .append("declare-fun")
                .append(Doc::space())
                .append(variable)
                .append(Doc::space())
                .append(
                    Doc::text("(")
                        .append(
                            Doc::nil()
                                .append(Doc::intersperse(
                                    arguments.iter().map(|arg| arg.to_doc()),
                                    Doc::line(),
                                ))
                                .nest(1)
                                .group(),
                        )
                        .append(")"),
                )
                .append(Doc::space())
                .append(output_type.to_doc())
                .append(")"),
            VmtCommands::DefineFun {
                variable,
                arguments,
                output_type,
                definition,
                flags,
            } => Doc::text("(")
                .append("define-fun")
                .append(Doc::space())
                .append(variable)
                .append(Doc::space())
                .append(
                    Doc::text("(")
                        .append(
                            Doc::nil()
                                .append(Doc::intersperse(
                                    arguments.iter().map(|arg| arg.to_doc()),
                                    Doc::line(),
                                ))
                                .nest(1)
                                .group(),
                        )
                        .append(")"),
                )
                .append(Doc::space())
                .append(output_type.to_doc())
                .append(Doc::space())
                .append(
                    Doc::text("(")
                        .append("!")
                        .append(
                            Doc::line()
                                .append(definition.to_doc())
                                .append(
                                    Doc::line()
                                        .append(Doc::intersperse(
                                            flags.iter().map(|(flag, value)| {
                                                Doc::text(flag).append(Doc::space()).append(value)
                                            }),
                                            Doc::line(),
                                        ))
                                        .group(),
                                )
                                .nest(1)
                                .group(),
                        )
                        .append(")"),
                )
                .append(")"),
        }
    }
}

// fn format_output_type(output_type: &[String]) -> Doc {
//     if output_type.is_empty() {
//         Doc::nil()
//     } else if output_type.len() == 1 {
//         Doc::text(&output_type[0])
//     } else {
//         Doc::text("(")
//             .append(
//                 Doc::nil()
//                     .append(Doc::intersperse(output_type.iter(), Doc::line()))
//                     .nest(1)
//                     .group(),
//             )
//             .append(")")
//     }
// }
