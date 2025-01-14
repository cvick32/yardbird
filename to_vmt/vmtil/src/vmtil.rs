//! The VMT Intermediate language for building up VMT programs from Rust source

use std::{collections::HashMap, mem};

use proc_macro2::TokenStream;
use quote::quote;
use smt2parser::{concrete, vmt::VMTModel, CommandStream};

use crate::{
    context::{BuildContextual, Context},
    pretty_printer::{ToDoc, VmtCommands},
};

#[derive(Default, Debug, Clone)]
pub struct VmtilBuilder {
    variables: Vec<String>,
    immutable_variables: Vec<String>,
    type_context: HashMap<String, Type>,
    initial_conditions: Vec<BooleanExpr>,
    transition_conditions: Vec<BooleanExpr>,
    property_preconditions: Vec<BooleanExpr>,
    property: Vec<BooleanExpr>,
}

impl VmtilBuilder {
    pub fn var_immut(&mut self, var_name: impl ToString, type_name: impl Into<Type>) -> &mut Self {
        let next_var = format!("{}_next", var_name.to_string());
        self.immutable_variables.push(var_name.to_string());
        self.type_context
            .insert(var_name.to_string(), type_name.into());
        self.transition_conditions
            .push(BooleanExpr::binop("=", var_name, next_var));
        self
    }

    pub fn var_mut(&mut self, var_name: impl ToString, type_name: impl Into<Type>) -> &mut Self {
        self.variables.push(var_name.to_string());
        self.type_context
            .insert(var_name.to_string(), type_name.into());
        self
    }

    /// TODO: right now we really only support a single stmt, we will need something like a PC
    /// to do this properly I think
    pub fn stmt(&mut self, stmt: impl BuildContextual) -> &mut Self {
        let mut context = Context::default();
        let cond = stmt.extend(&mut context, self);
        self.transition_conditions.push(cond);
        self
    }

    /// TODO: A hack until we have proper multi-statement support
    pub fn local_binding(
        &mut self,
        var_name: impl ToString,
        type_name: impl Into<Type>,
        expr: impl Into<Expr>,
    ) -> &mut Self {
        self.variables.push(var_name.to_string());
        self.type_context
            .insert(var_name.to_string(), type_name.into());
        self.initial_conditions
            .push(BooleanExpr::binop("=", var_name.to_string(), expr));
        self
    }

    pub fn post_condition(&mut self, boolean_stmt: BooleanExpr) -> &mut Self {
        if let BooleanExpr::Forall { quantified, expr } = boolean_stmt {
            self.var_immut(quantified.clone(), Type::Int);
            self.property_preconditions.push(BooleanExpr::binop(
                "<",
                BooleanExpr::Lit("0".to_string()),
                quantified.clone(),
            ));
            self.property.push(*expr);
        } else {
            self.property.push(boolean_stmt);
        }
        self
    }

    pub fn build_model(mut self, dump_vmt: bool) -> VMTModel {
        // correct the case of variables according to their mutability
        self.initial_conditions = mem::take(&mut self.initial_conditions)
            .into_iter()
            .map(|expr| expr.rewrite_w_mutability(&self))
            .collect();
        self.transition_conditions = mem::take(&mut self.transition_conditions)
            .into_iter()
            .map(|expr| expr.rewrite_w_mutability(&self))
            .collect();
        self.property_preconditions = mem::take(&mut self.property_preconditions)
            .into_iter()
            .map(|expr| expr.rewrite_w_mutability(&self))
            .collect();
        self.property = mem::take(&mut self.property)
            .into_iter()
            .map(|expr| expr.rewrite_w_mutability(&self))
            .collect();

        let vmt_string = format!("{self}");
        if dump_vmt {
            println!("{}", vmt_string)
        }
        let command_stream =
            CommandStream::new(vmt_string.as_bytes(), concrete::SyntaxBuilder, None);

        VMTModel::checked_from(
            command_stream
                .into_iter()
                .collect::<Result<Vec<_>, concrete::Error>>()
                .unwrap(),
        )
        .unwrap()
    }

    fn rewrite(&self, var: String) -> String {
        let (base, suffix) = if let Some(base) = var.strip_suffix("_next") {
            (base.to_string(), "_next")
        } else {
            (var.clone(), "")
        };

        if self.variables.contains(&base) {
            format!("{}{suffix}", base.to_lowercase())
        } else if self.immutable_variables.contains(&base) {
            format!("{}{suffix}", base.to_uppercase())
        } else {
            panic!(
                "Unknown variable: mut {:?} immut {:?} {base}",
                self.variables, self.immutable_variables
            )
        }
    }

    pub fn get_type(&self, var: &str) -> &Type {
        if let Some(var) = var.strip_suffix("_next") {
            &self.type_context[var]
        } else {
            &self.type_context[var]
        }
    }
}

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

    fn rewrite_w_mutability(self, builder: &VmtilBuilder) -> Self {
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

    fn rewrite_w_mutability(self, builder: &VmtilBuilder) -> Self {
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
                builder.var_mut(loop_var.clone(), Type::Int);
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
                                    Expr::arith_binop("+", loop_var, Expr::Lit("1".to_string())),
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
        for var in self.variables.iter() {
            writeln!(
                f,
                "{}",
                VmtCommands::DeclareFun {
                    variable: var.to_string(),
                    arguments: vec![],
                    output_type: self.get_type(var).clone(),
                }
                .to_doc()
                .pretty(80)
            )?;
            writeln!(
                f,
                "{}",
                VmtCommands::DeclareFun {
                    variable: format!("{}_next", var),
                    arguments: vec![],
                    output_type: self.get_type(var).clone()
                }
                .to_doc()
                .pretty(80)
            )?;
            writeln!(
                f,
                "{}",
                VmtCommands::DefineFun {
                    variable: format!(".{var}"),
                    arguments: vec![],
                    output_type: self.get_type(var).clone(),
                    definition: BooleanExpr::Var(var.to_string()),
                    flags: vec![(":next".to_string(), format!("{var}_next"))]
                }
                .to_doc()
                .pretty(80)
            )?;
        }
        for var in self.immutable_variables.iter() {
            let upper_var = if let Some(base_var) = var.strip_suffix("_next") {
                base_var.to_uppercase()
            } else {
                var.to_uppercase()
            };
            writeln!(
                f,
                "{}",
                VmtCommands::DeclareFun {
                    variable: upper_var.clone(),
                    arguments: vec![],
                    output_type: self.get_type(var).clone(),
                }
                .to_doc()
                .pretty(80)
            )?;
            writeln!(
                f,
                "{}",
                VmtCommands::DeclareFun {
                    variable: format!("{upper_var}_next"),
                    arguments: vec![],
                    output_type: self.get_type(var).clone()
                }
                .to_doc()
                .pretty(80)
            )?;
            writeln!(
                f,
                "{}",
                VmtCommands::DefineFun {
                    variable: format!(".{upper_var}"),
                    arguments: vec![],
                    output_type: self.get_type(var).clone(),
                    definition: BooleanExpr::Var(upper_var.clone()),
                    flags: vec![(":next".to_string(), format!("{upper_var}_next"))]
                }
                .to_doc()
                .pretty(80)
            )?;
        }
        writeln!(
            f,
            "{}",
            VmtCommands::DefineFun {
                variable: "init".to_string(),
                arguments: vec![],
                output_type: Type::Bool,
                definition: BooleanExpr::Conjunction(self.initial_conditions.clone()),
                flags: vec![(":init".to_string(), "true".to_string())]
            }
            .to_doc()
            .pretty(80)
        )?;
        writeln!(
            f,
            "{}",
            VmtCommands::DefineFun {
                variable: "trans".to_string(),
                arguments: vec![],
                output_type: Type::Bool,
                definition: BooleanExpr::Conjunction(self.transition_conditions.clone()),
                flags: vec![(":trans".to_string(), "true".to_string())]
            }
            .to_doc()
            .pretty(80)
        )?;
        writeln!(
            f,
            "{}",
            VmtCommands::DefineFun {
                variable: "prop".to_string(),
                arguments: vec![],
                output_type: Type::Bool,
                definition: BooleanExpr::binop(
                    "=>",
                    BooleanExpr::Conjunction(self.property_preconditions.clone()),
                    BooleanExpr::Conjunction(self.property.clone())
                ),
                flags: vec![(":invar-property".to_string(), "0".to_string())]
            }
            .to_doc()
            .pretty(80)
        )?;
        Ok(())
    }
}

impl quote::ToTokens for Type {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Type::Int => tokens.extend(quote! { ::to_vmt::vmtil::Type::Int }),
            Type::Bool => tokens.extend(quote! { ::to_vmt::vmtil::Type::Bool }),
            Type::Array { index, value } => tokens.extend(quote! {
                ::to_vmt::vmtil::Type::Array {
                    index: Box::new(#index),
                    value: Box::new(#value)
                }
            }),
        }
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
                    var: #var.to_string(),
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
            } => {
                let false_tokens = false_branch
                    .as_ref()
                    .map(|stmt| quote!(Some(Box::new(#stmt))))
                    .unwrap_or_else(|| quote!(None));
                tokens.extend(quote! {
                    ::to_vmt::vmtil::Stmt::If {
                        condition: #condition,
                        true_branch: Box::new(#true_branch),
                        false_branch: #false_tokens
                    }
                })
            }
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
            Expr::Lit(lit) => tokens.extend(quote! {
                ::to_vmt::vmtil::Expr::Lit(#lit.to_string())
            }),
            Expr::Boolean(boolean_expr) => tokens.extend(quote! {
                ::to_vmt::vmtil::Expr::Boolean(Box::new(#boolean_expr))
            }),
            Expr::ArithBinop { op, lhs, rhs } => tokens.extend(quote! {
                ::to_vmt::vmtil::Expr::ArithBinop {
                    op: #op.to_string(),
                    lhs: Box::new(#lhs),
                    rhs: Box::new(#rhs)
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
            BooleanExpr::Forall { quantified, expr } => tokens.extend(quote! {
                ::to_vmt::vmtil::BooleanExpr::Forall {
                    quantified: #quantified.to_string(),
                    expr: Box::new(#expr)
                }
            }),
            BooleanExpr::Var(var) => tokens.extend(quote! {
                ::to_vmt::vmtil::BooleanExpr::Var(#var.to_string())
            }),
            BooleanExpr::Lit(lit) => tokens.extend(quote! {
                ::to_vmt::vmtil::BooleanExpr::Var(#lit.to_string())
            }),
            BooleanExpr::Binop { op, lhs, rhs } => tokens.extend(quote! {
                ::to_vmt::vmtil::BooleanExpr::Binop {
                    op: #op.to_string(),
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
            .var_immut(
                "A",
                Type::Array {
                    index: Box::new(Type::Int),
                    value: Box::new(Type::Int),
                },
            )
            .var_immut("N", Type::Int)
            .var_mut(
                "b",
                Type::Array {
                    index: Box::new(Type::Int),
                    value: Box::new(Type::Int),
                },
            )
            .stmt(Stmt::for_loop(
                "i",
                "0",
                "N",
                Stmt::store("b", "i", Expr::select("A", "i")),
            ))
            .post_condition(BooleanExpr::forall(
                "Z",
                BooleanExpr::binop("=", Expr::select("a", "Z"), Expr::select("b", "Z")),
            ));
        println!("{builder}");
        let model = builder.build_model();
        println!("{}", model.as_vmt_string());
        assert_eq!(model.as_vmt_string(), "")
    }
}
