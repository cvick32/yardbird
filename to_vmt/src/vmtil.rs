//! The VMT Intermediate language for building up VMT programs from Rust source

use std::{collections::HashSet, mem};

use smt2parser::vmt::VMTModel;

use crate::pretty_printer::ToDoc;

#[derive(Default, Debug)]
pub struct VmtilBuilder {
    variables: Vec<String>,
    immutable_variables: Vec<String>,
    initial_conditions: Vec<BooleanExpr>,
    transition_conditions: Vec<BooleanExpr>,
    property_preconditions: Vec<BooleanExpr>,
    property: Vec<BooleanExpr>,
}

#[derive(Default)]
pub struct Context {
    scopes: Vec<Option<HashSet<String>>>,
    current_scope: Option<ScopeHandle>,
}

#[derive(Clone, Copy)]
struct ScopeHandle(usize);

pub trait BuildContextual {
    fn extend(self, context: &mut Context, builder: &mut VmtilBuilder) -> BooleanExpr;
}

impl Context {
    fn new_scope(&mut self) -> ScopeHandle {
        let new_scope = HashSet::default();
        let handle = ScopeHandle(self.scopes.len());
        self.scopes.push(Some(new_scope));
        self.current_scope = Some(handle);
        handle
    }

    fn pop_scope(&mut self, handle: ScopeHandle) -> HashSet<String> {
        let vars = mem::take(&mut self.scopes[handle.0]);
        self.current_scope = None;
        vars.expect("Scope didn't exist!")
    }

    fn add_write_to(&mut self, var: String) {
        if let Some(scope) = self.current_scope {
            self.scopes[scope.0]
                .as_mut()
                .expect("Scope didn't exist!")
                .insert(var);
        }
    }
}

impl VmtilBuilder {
    pub fn var_immut(mut self, var_name: impl ToString) -> Self {
        self.variables.push(var_name.to_string());
        let next_var = format!("{}_next", var_name.to_string());
        self.transition_conditions.push(BooleanExpr::Binop {
            op: "=".to_string(),
            lhs: Expr::Var(var_name.to_string()),
            rhs: Expr::Var(next_var),
        });
        self
    }

    pub fn var_mut(mut self, var_name: impl ToString) -> Self {
        self.immutable_variables.push(var_name.to_string());
        self
    }

    pub fn stmt(mut self, stmt: impl BuildContextual) -> Self {
        let mut context = Context::default();
        let cond = stmt.extend(&mut context, &mut self);
        self.transition_conditions.push(cond);
        self
    }

    pub fn post_condition(mut self, boolean_stmt: BooleanExpr) -> Self {
        if let BooleanExpr::Forall { quantified, expr } = boolean_stmt {
            self = self.var_immut(quantified.clone());
            self.property_preconditions.push(BooleanExpr::Binop {
                op: "<".to_string(),
                lhs: Expr::Var("0".to_string()),
                rhs: Expr::Var(quantified.clone()),
            });
            self.property_preconditions.push(BooleanExpr::Binop {
                op: "<".to_string(),
                lhs: Expr::Var(quantified.clone()),
                // TODO: not sure how to do this by default
                rhs: Expr::Var("N".to_string()),
            });
            self.property.push(*expr);
        } else {
            self.property.push(boolean_stmt);
        }
        self
    }

    pub fn build_model(self) -> VMTModel {
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
    If {
        condition: BooleanExpr,
        true_branch: Box<Stmt>,
        false_branch: Option<Box<Stmt>>,
    },
    ArrayLoop {
        index: String,
        lower_bound: String,
        upper_bound: String,
        body: Box<Stmt>,
    },
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

#[derive(Clone, Debug)]
pub enum BooleanExpr {
    Forall {
        quantified: String,
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
                BooleanExpr::Binop {
                    op: "=".to_string(),
                    lhs: Expr::Var(format!("{array}_next")),
                    rhs: Expr::Store {
                        array,
                        index,
                        expr: Box::new(expr),
                    },
                }
            }
            Stmt::Loop(stmt) => todo!(),
            Stmt::If {
                condition,
                true_branch,
                false_branch,
            } => {
                let mut conditions = vec![];
                let true_scope = context.new_scope();
                conditions.push(BooleanExpr::Binop {
                    op: "=>".to_string(),
                    lhs: Expr::Boolean(Box::new(condition.clone())),
                    rhs: Expr::Boolean(Box::new(true_branch.extend(context, builder))),
                });
                let true_br_variables = context.pop_scope(true_scope);

                if let Some(stmt) = false_branch {
                    let false_scope = context.new_scope();
                    let rhs = stmt.extend(context, builder);
                    let false_br_variables = context.pop_scope(false_scope);
                    // this name might be wrong, will ask cole about it
                    // probably want some semblance of scoping
                    let mut frame_conditions = vec![rhs];
                    frame_conditions.extend(true_br_variables.difference(&false_br_variables).map(
                        |var| {
                            let var_next = format!("{var}_next");
                            BooleanExpr::Binop {
                                op: "=".to_string(),
                                lhs: Expr::Var(var.clone()),
                                rhs: Expr::Var(var_next),
                            }
                        },
                    ));
                    conditions.push(BooleanExpr::Binop {
                        op: "=>".to_string(),
                        lhs: Expr::Boolean(Box::new(BooleanExpr::Not(Box::new(condition.clone())))),
                        rhs: Expr::Boolean(Box::new(BooleanExpr::Conjunction(frame_conditions))),
                    });
                } else {
                    let const_frame_conditions = true_br_variables
                        .into_iter()
                        .map(|var| {
                            let var_next = format!("{var}_next");
                            BooleanExpr::Binop {
                                op: "=".to_string(),
                                lhs: Expr::Var(var),
                                rhs: Expr::Var(var_next),
                            }
                        })
                        .collect();
                    conditions.push(BooleanExpr::Binop {
                        op: "=>".to_string(),
                        lhs: Expr::Boolean(Box::new(BooleanExpr::Not(Box::new(condition.clone())))),
                        rhs: Expr::Boolean(Box::new(BooleanExpr::Conjunction(
                            const_frame_conditions,
                        ))),
                    });
                }

                builder
                    .property_preconditions
                    .push(BooleanExpr::Not(Box::new(condition)));

                BooleanExpr::Conjunction(conditions)
            }
            Stmt::ArrayLoop {
                index,
                lower_bound,
                upper_bound,
                body,
            } => todo!(),
            Stmt::Assign { var, rhs } => {
                context.add_write_to(var.clone());
                BooleanExpr::Binop {
                    op: "=".to_string(),
                    lhs: Expr::Var(format!("{var}_next")),
                    rhs,
                }
            }
        }
        // match self {
        //     Stmt::Block { exprs } => {
        //         for e in exprs {
        //             e.extend(builder);
        //         }
        //     }
        //     Stmt::Store { array, index, expr } => todo!(),
        //     Stmt::ArrayLoop {
        //         index,
        //         lower_bound,
        //         upper_bound,
        //         body,
        //     } => {}
        // }
    }
}

impl std::fmt::Display for VmtilBuilder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
            BooleanExpr::Binop {
                op: "=>".to_string(),
                lhs: Expr::Boolean(Box::new(BooleanExpr::Conjunction(
                    self.property_preconditions.clone()
                ))),
                rhs: Expr::Boolean(Box::new(BooleanExpr::Conjunction(self.property.clone())))
            }
            .to_doc()
            .pretty(80)
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn play_array_copy() {
        let builder = VmtilBuilder::default()
            .var_immut("A")
            .var_immut("N")
            .var_mut("b")
            .stmt(Stmt::If {
                condition: BooleanExpr::Binop {
                    op: "<".to_string(),
                    lhs: Expr::Var("i".to_string()),
                    rhs: Expr::Var("N".to_string()),
                },
                true_branch: Box::new(Stmt::Block {
                    stmts: vec![
                        Stmt::Store {
                            array: "b".to_string(),
                            index: "i".to_string(),
                            expr: Expr::Select {
                                array: "A".to_string(),
                                index: "i".to_string(),
                            },
                        },
                        Stmt::Assign {
                            var: "i".to_string(),
                            rhs: Expr::ArithBinop {
                                op: "+".to_string(),
                                lhs: Box::new(Expr::Var("i".to_string())),
                                rhs: Box::new(Expr::Var("1".to_string())),
                            },
                        },
                    ],
                }),
                false_branch: None, // index: "i".to_string(),
                                    // lower_bound: "0".to_string(),
                                    // upper_bound: "N".to_string(),
                                    // body: Box::new(Stmt::Block {
                                    //     exprs: vec![Stmt::Store {
                                    //         array: "b".to_string(),
                                    //         index: "i".to_string(),
                                    //         expr: Expr::Select {
                                    //             array: "a".to_string(),
                                    //             index: "i".to_string(),
                                    //         },
                                    //     }],
                                    // }),
            })
            .post_condition(BooleanExpr::Forall {
                quantified: "Z".to_string(),
                expr: Box::new(BooleanExpr::Binop {
                    op: "=".to_string(),
                    lhs: Expr::Select {
                        array: "a".to_string(),
                        index: "Z".to_string(),
                    },
                    rhs: Expr::Select {
                        array: "b".to_string(),
                        index: "Z".to_string(),
                    },
                }),
            });
        println!("{builder}");
        let model = builder.build_model();
        println!("{}", model.as_vmt_string());
        assert_eq!(model.as_vmt_string(), "")
    }
}
