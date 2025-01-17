use std::{collections::HashSet, mem};

use crate::vmtil::{BooleanExpr, Expr, VmtilBuilder};

#[derive(Default)]
pub struct Context {
    scopes: Vec<Option<Scope>>,
    current_scope: Option<ScopeHandle>,
}

#[derive(Default)]
pub struct Scope {
    written_vars: HashSet<String>,
    facts: Vec<BooleanExpr>,
}

#[derive(Clone, Copy)]
pub struct ScopeHandle(usize);

pub trait BuildContextual {
    fn extend(self, context: &mut Context, builder: &mut VmtilBuilder) -> BooleanExpr;
}

impl Context {
    fn new_scope(&mut self) -> ScopeHandle {
        let new_scope = Scope::default();
        let handle = ScopeHandle(self.scopes.len());
        self.scopes.push(Some(new_scope));
        self.current_scope = Some(handle);
        handle
    }

    fn pop_scope(&mut self, handle: ScopeHandle) -> Scope {
        let vars = mem::take(&mut self.scopes[handle.0]);
        self.current_scope = None;
        vars.expect("Scope didn't exist!")
    }

    pub fn with_scope<F, T>(&mut self, action: F) -> (Scope, T)
    where
        F: FnOnce(&mut Self) -> T,
    {
        let handle = self.new_scope();
        let t = action(self);
        (self.pop_scope(handle), t)
    }

    pub fn add_write_to(&mut self, var: String) {
        if let Some(scope) = self.current_scope {
            self.scopes[scope.0]
                .as_mut()
                .expect("Scope didn't exist!")
                .written_vars
                .insert(var);
        }
    }

    pub fn add_fact(&mut self, fact: BooleanExpr) {
        if let Some(scope) = self.current_scope {
            self.scopes[scope.0]
                .as_mut()
                .expect("Scope didn't exist!")
                .facts
                .push(fact);
        }
    }

    pub fn current_facts(&self) -> Option<&[BooleanExpr]> {
        self.current_scope.map(|scope| {
            self.scopes[scope.0]
                .as_ref()
                .expect("Scope didn't exist!")
                .facts
                .as_slice()
        })
    }

    // TODO: is this function needed, if we add frame conditions
    // for all mutable variables?
    pub fn get_written_vars(&self) -> Option<HashSet<String>> {
        self.current_scope.map(|scope| {
            self.scopes[scope.0]
                .as_ref()
                .expect("Scope didn't exist!")
                .written_vars
                .clone()
        })
    }
}

impl Scope {
    pub fn frame_conditions(&self) -> impl Iterator<Item = BooleanExpr> + '_ {
        self.written_vars.iter().map(|var| {
            let var_next = format!("{var}_next");
            BooleanExpr::Binop {
                op: "=".to_string(),
                lhs: Expr::Var(var.clone()),
                rhs: Expr::Var(var_next),
            }
        })
    }

    pub fn frame_conditions_without<'a>(
        &'a self,
        other: &'a Self,
    ) -> impl Iterator<Item = BooleanExpr> + 'a {
        self.written_vars
            .difference(&other.written_vars)
            .map(|var| {
                let var_next = format!("{var}_next");
                BooleanExpr::Binop {
                    op: "=".to_string(),
                    lhs: Expr::Var(var.clone()),
                    rhs: Expr::Var(var_next),
                }
            })
    }
}
