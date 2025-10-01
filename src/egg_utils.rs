use egg::CostFunction;

pub trait Saturate<CF, L>
where
    CF: CostFunction<L, Cost = u32> + Clone,
    L: egg::Language,
{
    type Ret;
    fn saturate(&mut self, cost: CF, refinement_step: u32) -> Self::Ret;
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
