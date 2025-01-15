use crate::VmtilBuilder;

#[derive(Clone, Debug)]
pub enum Type {
    Int,
    Bool,
    Array { index: Box<Type>, value: Box<Type> },
}

#[derive(Clone, Debug)]
pub enum Stmt {
    Block {
        stmts: Vec<Stmt>,
    },
    Store {
        array: String,
        index: String,
        expr: Expr,
    },
    Assign {
        var: String,
        rhs: Expr,
    },
    Loop(Box<Stmt>),
    ForLoop {
        loop_var: String,
        lower_bound: Expr,
        upper_bound: Expr,
        body: Box<Stmt>,
    },
    Break,
    If {
        condition: BooleanExpr,
        true_branch: Box<Stmt>,
        false_branch: Option<Box<Stmt>>,
    },
}

impl Stmt {
    pub fn store(array: impl ToString, index: impl ToString, expr: impl Into<Expr>) -> Self {
        Self::Store {
            array: array.to_string(),
            index: index.to_string(),
            expr: expr.into(),
        }
    }

    pub fn assign(var: impl ToString, rhs: impl Into<Expr>) -> Self {
        Self::Assign {
            var: var.to_string(),
            rhs: rhs.into(),
        }
    }

    pub fn loop_stmt(stmt: impl Into<Stmt>) -> Self {
        Self::Loop(Box::new(stmt.into()))
    }

    pub fn for_loop(
        loop_var: impl ToString,
        lower_bound: impl Into<Expr>,
        upper_bound: impl Into<Expr>,
        body: impl Into<Stmt>,
    ) -> Self {
        Self::ForLoop {
            loop_var: loop_var.to_string(),
            lower_bound: lower_bound.into(),
            upper_bound: upper_bound.into(),
            body: Box::new(body.into()),
        }
    }

    pub fn if_stmt(
        condition: impl Into<BooleanExpr>,
        true_branch: impl Into<Stmt>,
        false_branch: Option<impl Into<Stmt>>,
    ) -> Self {
        Self::If {
            condition: condition.into(),
            true_branch: Box::new(true_branch.into()),
            false_branch: false_branch.map(|x| Box::new(x.into())),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Expr {
    Store {
        array: String,
        index: String,
        expr: Box<Expr>,
    },
    Select {
        array: String,
        index: String,
    },
    Var(String),
    Lit(String),
    Boolean(Box<BooleanExpr>),
    ArithBinop {
        op: String,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
}

impl Expr {
    pub fn store(array: impl ToString, index: impl ToString, expr: impl Into<Expr>) -> Self {
        Self::Store {
            array: array.to_string(),
            index: index.to_string(),
            expr: Box::new(expr.into()),
        }
    }

    pub fn select(array: impl ToString, index: impl ToString) -> Self {
        Self::Select {
            array: array.to_string(),
            index: index.to_string(),
        }
    }

    pub fn arith_binop(op: impl ToString, lhs: impl Into<Expr>, rhs: impl Into<Expr>) -> Self {
        Self::ArithBinop {
            op: op.to_string(),
            lhs: Box::new(lhs.into()),
            rhs: Box::new(rhs.into()),
        }
    }

    pub(super) fn rewrite_w_mutability(self, builder: &VmtilBuilder) -> Self {
        match self {
            Expr::Store { array, index, expr } => Expr::store(
                builder.rewrite(array),
                builder.rewrite(index),
                expr.rewrite_w_mutability(builder),
            ),
            Expr::Select { array, index } => {
                Expr::select(builder.rewrite(array), builder.rewrite(index))
            }
            Expr::Var(var) => Expr::Var(builder.rewrite(var)),
            Expr::Lit(lit) => Expr::Lit(lit),
            Expr::Boolean(boolean_expr) => {
                Expr::Boolean(Box::new(boolean_expr.rewrite_w_mutability(builder)))
            }
            Expr::ArithBinop { op, lhs, rhs } => Expr::arith_binop(
                op,
                lhs.rewrite_w_mutability(builder),
                rhs.rewrite_w_mutability(builder),
            ),
        }
    }
}

impl<S> From<S> for Expr
where
    S: ToString,
{
    fn from(value: S) -> Self {
        Expr::Var(value.to_string())
    }
}

impl From<BooleanExpr> for Expr {
    fn from(value: BooleanExpr) -> Self {
        Expr::Boolean(Box::new(value))
    }
}

#[derive(Clone, Debug)]
pub enum BooleanExpr {
    True,
    Forall {
        quantified: String,
        expr: Box<BooleanExpr>,
    },
    Var(String),
    Lit(String),
    Binop {
        op: String,
        lhs: Expr,
        rhs: Expr,
    },
    Conjunction(Vec<BooleanExpr>),
    Not(Box<BooleanExpr>),
}

impl BooleanExpr {
    pub fn forall(quantified: impl ToString, expr: impl Into<BooleanExpr>) -> Self {
        Self::Forall {
            quantified: quantified.to_string(),
            expr: Box::new(expr.into()),
        }
    }

    pub fn binop(op: impl ToString, lhs: impl Into<Expr>, rhs: impl Into<Expr>) -> Self {
        Self::Binop {
            op: op.to_string(),
            lhs: lhs.into(),
            rhs: rhs.into(),
        }
    }

    pub fn negate(expr: BooleanExpr) -> Self {
        Self::Not(Box::new(expr))
    }

    pub(super) fn rewrite_w_mutability(self, builder: &VmtilBuilder) -> Self {
        match self {
            BooleanExpr::True => BooleanExpr::True,
            BooleanExpr::Forall { quantified, expr } => BooleanExpr::forall(
                builder.rewrite(quantified),
                expr.rewrite_w_mutability(builder),
            ),
            BooleanExpr::Var(var) => BooleanExpr::Var(builder.rewrite(var)),
            BooleanExpr::Lit(lit) => BooleanExpr::Lit(lit),
            BooleanExpr::Binop { op, lhs, rhs } => BooleanExpr::binop(
                op,
                lhs.rewrite_w_mutability(builder),
                rhs.rewrite_w_mutability(builder),
            ),
            BooleanExpr::Conjunction(vec) => BooleanExpr::Conjunction(
                vec.into_iter()
                    .map(|conj| conj.rewrite_w_mutability(builder))
                    .collect(),
            ),
            BooleanExpr::Not(boolean_expr) => {
                BooleanExpr::negate(boolean_expr.rewrite_w_mutability(builder))
            }
        }
    }

    pub(super) fn simplify(self) -> Self {
        match self {
            BooleanExpr::True => BooleanExpr::True,
            BooleanExpr::Forall { quantified, expr } => BooleanExpr::Forall {
                quantified,
                expr: Box::new(expr.simplify()),
            },
            BooleanExpr::Var(var) => BooleanExpr::Var(var),
            BooleanExpr::Lit(lit) => BooleanExpr::Lit(lit),
            BooleanExpr::Binop {
                op,
                lhs: Expr::Boolean(lhs),
                rhs: Expr::Boolean(rhs),
            } => match op.as_str() {
                "=>" if rhs.is_trivial() => BooleanExpr::True,
                op => BooleanExpr::Binop {
                    op: op.to_string(),
                    lhs: Expr::Boolean(Box::new(lhs.simplify())),
                    rhs: Expr::Boolean(Box::new(rhs.simplify())),
                },
            },
            BooleanExpr::Conjunction(vec) => BooleanExpr::Conjunction(
                vec.into_iter()
                    .map(BooleanExpr::simplify)
                    .flat_map(|x| {
                        if let BooleanExpr::Conjunction(vec) = x {
                            vec
                        } else {
                            vec![x]
                        }
                    })
                    .filter(|x| !x.is_trivial())
                    .collect(),
            ),
            BooleanExpr::Not(expr) => BooleanExpr::Not(Box::new(expr.simplify())),
            x => x,
        }
    }

    fn is_trivial(&self) -> bool {
        match self {
            BooleanExpr::True => true,
            BooleanExpr::Var(_)
            | BooleanExpr::Lit(_)
            | BooleanExpr::Forall { .. }
            | BooleanExpr::Binop { .. }
            | BooleanExpr::Not(_) => false,
            BooleanExpr::Conjunction(vec) => vec.iter().all(BooleanExpr::is_trivial),
        }
    }
}
