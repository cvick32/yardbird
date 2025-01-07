use crate::cost_functions::{symbol_cost::BestSymbolSubstitution, term_cost::BestTermSubstitution};

/// Trait for saturating an egraph with the array axioms. This hides the details of
/// needing to create a runner every time you want to saturate a set of rules on an egraph.
pub trait Saturate {
    type Ret;
    fn saturate_symbol(&mut self, cost: BestSymbolSubstitution) -> Self::Ret;

    fn saturate_term(&mut self, cost: BestTermSubstitution) -> Self::Ret;
}

pub trait RecExprRoot<L> {
    fn root(&self) -> &L;
}

impl<L> RecExprRoot<L> for egg::RecExpr<L> {
    fn root(&self) -> &L {
        let ast_nodes = self.as_ref();
        &ast_nodes[ast_nodes.len() - 1]
    }
}
