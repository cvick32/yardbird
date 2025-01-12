//! The VMT Intermediate language for building up VMT programs from Rust source

use proc_macro2::TokenStream;
use quote::quote;
use smt2parser::vmt::VMTModel;

use crate::{
    context::{BuildContextual, Context},
    pretty_printer::ToDoc,
};

#[derive(Default, Debug)]
pub struct VmtilBuilder {
    variables: Vec<String>,
    immutable_variables: Vec<String>,
    initial_conditions: Vec<BooleanExpr>,
    transition_conditions: Vec<BooleanExpr>,
    property_preconditions: Vec<BooleanExpr>,
    property: Vec<BooleanExpr>,
}

impl VmtilBuilder {
    pub fn var_immut(&mut self, var_name: impl ToString) -> &mut Self {
        self.variables.push(var_name.to_string());
        let next_var = format!("{}_next", var_name.to_string());
        self.transition_conditions
            .push(BooleanExpr::binop("=", var_name, next_var));
        self
    }

    pub fn var_mut(&mut self, var_name: impl ToString) -> &mut Self {
        self.immutable_variables.push(var_name.to_string());
        self
    }

    pub fn stmt(&mut self, stmt: impl BuildContextual) -> &mut Self {
        let mut context = Context::default();
        let cond = stmt.extend(&mut context, self);
        self.transition_conditions.push(cond);
        self
    }

    // pub fn for_loop(
    //     mut self,
    //     loop_var: impl ToString,
    //     lower_bound: impl Into<Expr>,
    //     upper_bound: impl Into<Expr>,
    //     body: impl Into<Stmt>,
    // ) -> Self {
    //     let loop_var = loop_var.to_string();
    //     self = self.var_mut(loop_var.clone());
    //     self.initial_conditions
    //         .push(BooleanExpr::binop("=", loop_var.clone(), lower_bound));
    //     let loop_translation = Stmt::loop_stmt(Stmt::Block {
    //         stmts: vec![Stmt::if_stmt(
    //             BooleanExpr::binop("<", loop_var.clone(), upper_bound),
    //             Stmt::Block {
    //                 stmts: vec![
    //                     body.into(),
    //                     Stmt::assign(loop_var.clone(), Expr::arith_binop("+", loop_var, "1")),
    //                 ],
    //             },
    //             Some(Stmt::Break),
    //         )],
    //     });
    //     self.stmt(loop_translation)
    // }

    pub fn post_condition(&mut self, boolean_stmt: BooleanExpr) -> &mut Self {
        if let BooleanExpr::Forall {
            quantified,
            bound,
            expr,
        } = boolean_stmt
        {
            self.var_immut(quantified.clone());
            self.property_preconditions
                .push(BooleanExpr::binop("<", "0", quantified.clone()));
            if let Some(bound) = bound {
                self.property_preconditions.push(BooleanExpr::binop(
                    "<",
                    quantified.clone(),
                    bound,
                ));
            }
            self.property.push(*expr);
        } else {
            self.property.push(boolean_stmt);
        }
        self
    }

    pub fn build_model(self) -> VMTModel {
        println!("{self}");
        todo!()
    }
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
        bound: Option<String>,
        expr: Box<BooleanExpr>,
    },
    Binop {
        op: String,
        lhs: Expr,
        rhs: Expr,
    },
    Conjunction(Vec<BooleanExpr>),
    Not(Box<BooleanExpr>),
}

impl BooleanExpr {
    pub fn forall(
        quantified: impl ToString,
        bound: Option<impl ToString>,
        expr: impl Into<BooleanExpr>,
    ) -> Self {
        Self::Forall {
            quantified: quantified.to_string(),
            bound: bound.map(|x| x.to_string()),
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
}

impl BuildContextual for Stmt {
    fn extend(self, context: &mut Context, builder: &mut VmtilBuilder) -> BooleanExpr {
        match self {
            Stmt::Block { stmts } => BooleanExpr::Conjunction(
                stmts
                    .into_iter()
                    .map(|expr| expr.extend(context, builder))
                    .collect(),
            ),
            Stmt::Store { array, index, expr } => {
                context.add_write_to(array.clone());
                BooleanExpr::binop(
                    "=",
                    format!("{array}_next"),
                    Expr::store(array, index, expr),
                )
            }
            Stmt::Loop(stmt) => stmt.extend(context, builder),
            Stmt::ForLoop {
                loop_var,
                lower_bound,
                upper_bound,
                body,
            } => {
                builder.var_mut(loop_var.clone());
                builder.initial_conditions.push(BooleanExpr::binop(
                    "=",
                    loop_var.clone(),
                    lower_bound,
                ));
                let loop_translation = Stmt::loop_stmt(Stmt::Block {
                    stmts: vec![Stmt::if_stmt(
                        BooleanExpr::binop("<", loop_var.clone(), upper_bound),
                        Stmt::Block {
                            stmts: vec![
                                *body,
                                Stmt::assign(
                                    loop_var.clone(),
                                    Expr::arith_binop("+", loop_var, "1"),
                                ),
                            ],
                        },
                        Some(Stmt::Break),
                    )],
                });
                loop_translation.extend(context, builder)
            }
            Stmt::Break => {
                // this is only technically valid if we are in a loop. we are not checking that
                // explicitly however, Rust prevents you from writing a break if you are not in a
                // loop, so we "should" be fine.
                if let Some(facts) = context.current_facts() {
                    builder
                        .property_preconditions
                        .push(BooleanExpr::Conjunction(facts.to_vec()));
                }
                BooleanExpr::True
            }
            Stmt::If {
                condition,
                true_branch,
                false_branch,
            } => {
                // handle true branch
                let mut conditions = vec![];
                let (tru_scope, _) = context.with_scope(|context| {
                    // context.add_fact(condition.clone());
                    conditions.push(BooleanExpr::binop(
                        "=>",
                        condition.clone(),
                        true_branch.extend(context, builder),
                    ));
                });

                // handle false branch
                if let Some(false_stmt) = false_branch {
                    let (fls_scope, rhs) = context.with_scope(|context| {
                        // TODO: this is potentially wrong...if you set the loop variable
                        // to something weird and then break, this condition might
                        // be wrong. the correct thing would be to record every mutating
                        // state as a fact, but I'll postpone this till later...
                        context.add_fact(BooleanExpr::negate(condition.clone()));
                        false_stmt.extend(context, builder)
                    });
                    let mut frame_conditions = vec![rhs];
                    // add frame conditions for variables written in true branch, but not
                    // false branch
                    frame_conditions.extend(tru_scope.frame_conditions_without(&fls_scope));
                    conditions.push(BooleanExpr::binop(
                        "=>",
                        BooleanExpr::negate(condition.clone()),
                        BooleanExpr::Conjunction(frame_conditions),
                    ));
                } else {
                    let const_frame_conditions = tru_scope.frame_conditions().collect();
                    conditions.push(BooleanExpr::binop(
                        "=>",
                        BooleanExpr::negate(condition.clone()),
                        BooleanExpr::Conjunction(const_frame_conditions),
                    ));
                }

                BooleanExpr::Conjunction(conditions)
            }
            Stmt::Assign { var, rhs } => {
                context.add_write_to(var.clone());
                BooleanExpr::binop("=", format!("{var}_next"), rhs)
            }
        }
    }
}

impl std::fmt::Display for VmtilBuilder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Initial:")?;
        writeln!(
            f,
            "{}",
            BooleanExpr::Conjunction(self.initial_conditions.clone())
                .to_doc()
                .pretty(80)
        )?;
        writeln!(f, "Transition:")?;
        writeln!(
            f,
            "{}",
            BooleanExpr::Conjunction(self.transition_conditions.clone())
                .to_doc()
                .pretty(80)
        )?;
        writeln!(f, "Property:")?;
        writeln!(
            f,
            "{}",
            BooleanExpr::binop(
                "=>",
                BooleanExpr::Conjunction(self.property_preconditions.clone()),
                BooleanExpr::Conjunction(self.property.clone())
            )
            .to_doc()
            .pretty(80)
        )?;
        Ok(())
    }
}
impl quote::ToTokens for Stmt {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Stmt::Block { stmts } => tokens.extend(quote! {
                ::to_vmt::vmtil::Stmt::Block {
                    stmts: vec![ #(#stmts),* ]
                }
            }),
            Stmt::Store { array, index, expr } => tokens.extend(quote! {
                ::to_vmt::vmtil::Stmt::Store {
                    array: #array.to_string(),
                    index: #index.to_string(),
                    expr: #expr
                }
            }),
            Stmt::Assign { var, rhs } => tokens.extend(quote! {
                ::to_vmt::vmtil::Stmt::Assign {
                    var: #var,
                    rhs: #rhs
                }
            }),
            Stmt::Loop(stmt) => tokens.extend(quote! {
                ::to_vmt::vmtil::Stmt::Loop(Box::new(#stmt))
            }),
            Stmt::ForLoop {
                loop_var,
                lower_bound,
                upper_bound,
                body,
            } => tokens.extend(quote! {
                ::to_vmt::vmtil::Stmt::ForLoop {
                    loop_var: #loop_var.to_string(),
                    lower_bound: #lower_bound,
                    upper_bound: #upper_bound,
                    body: Box::new(#body),
                }
            }),
            Stmt::Break => tokens.extend(quote! {
                ::to_vmt::vmtil::Stmt::Break
            }),
            Stmt::If {
                condition,
                true_branch,
                false_branch,
            } => tokens.extend(quote! {
                ::to_vmt::vmtil::Stmt::If {
                    condition: #condition,
                    true_branch: #true_branch,
                    false_branch: #false_branch
                }
            }),
        }
    }
}

impl quote::ToTokens for Expr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Expr::Store { array, index, expr } => tokens.extend(quote! {
                ::to_vmt::vmtil::Expr::Store {
                    array: #array.to_string(),
                    index: #index.to_string(),
                    expr: #expr
                }
            }),
            Expr::Select { array, index } => tokens.extend(quote! {
                ::to_vmt::vmtil::Expr::Select {
                    array: #array.to_string(),
                    index: #index.to_string()
                }
            }),
            Expr::Var(var) => tokens.extend(quote! {
                ::to_vmt::vmtil::Expr::Var(#var.to_string())
            }),
            Expr::Boolean(boolean_expr) => tokens.extend(quote! {
                ::to_vmt::vmtil::Expr::Boolean(#boolean_expr)
            }),
            Expr::ArithBinop { op, lhs, rhs } => tokens.extend(quote! {
                ::to_vmt::vmtil::Expr::ArithBinop {
                    op: #op.to_string(),
                    lhs: #lhs,
                    rhs: #rhs
                }
            }),
        }
    }
}

impl quote::ToTokens for BooleanExpr {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            BooleanExpr::True => tokens.extend(quote! {
                ::to_vmt::vmtil::BooleanExpr::True
            }),
            BooleanExpr::Forall {
                quantified,
                bound,
                expr,
            } => tokens.extend(quote! {
                ::to_vmt::vmtil::BooleanExpr::Forall {
                    quantified: #quantified,
                    bound: #bound,
                    expr: #expr
                }
            }),
            BooleanExpr::Binop { op, lhs, rhs } => tokens.extend(quote! {
                ::to_vmt::vmtil::BooleanExpr::Binop {
                    op: #op,
                    lhs: #lhs,
                    rhs: #rhs
                }
            }),
            BooleanExpr::Conjunction(vec) => tokens.extend(quote! {
                ::to_vmt::vmtil::BooleanExpr::Conjunction(vec![#(#vec)*])
            }),
            BooleanExpr::Not(boolean_expr) => tokens.extend(quote! {
                ::to_vmt::vmtil::BooleanExpr::Not(#boolean_expr)
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn play_array_copy() {
        let mut builder = VmtilBuilder::default();
        builder
            .var_immut("A")
            .var_immut("N")
            .var_mut("b")
            .stmt(Stmt::for_loop(
                "i",
                "0",
                "N",
                Stmt::store("b", "i", Expr::select("A", "i")),
            ))
            .post_condition(BooleanExpr::forall(
                "Z",
                Some("N"),
                BooleanExpr::binop("=", Expr::select("a", "Z"), Expr::select("b", "Z")),
            ));
        println!("{builder}");
        let model = builder.build_model();
        println!("{}", model.as_vmt_string());
        assert_eq!(model.as_vmt_string(), "")
    }
}
