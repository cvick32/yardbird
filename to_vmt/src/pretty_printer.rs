use pretty::RcDoc;

use crate::vmtil::{BooleanExpr, Expr};

pub type Doc<'a> = RcDoc<'a, ()>;

pub trait ToDoc {
    fn to_doc(&self) -> Doc;
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
            BooleanExpr::Conjunction(vec) if vec.len() == 1 => vec[0].to_doc(),
            BooleanExpr::Conjunction(vec) => Doc::text("(")
                .append("and")
                .append(
                    Doc::line()
                        .append(Doc::intersperse(
                            vec.iter().map(|ex| ex.to_doc()),
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
        }
    }
}
