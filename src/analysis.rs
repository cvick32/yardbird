use egg::{Analysis, DidMerge, EGraph, Id, Justification, Language};

#[derive(Default)]
pub struct SaturationInequalities;

impl<L: Language> Analysis<L> for SaturationInequalities {
    type Data = bool;
    fn make(_egraph: &EGraph<L, Self>, _enode: &L) -> Self::Data {
        false
    }
    fn merge(&mut self, a: &mut Self::Data, _b: Self::Data) -> DidMerge {
        *a = true;
        DidMerge(false, true)
    }

    fn pre_union(
        _egraph: &EGraph<L, Self>,
        _id1: Id,
        _id2: Id,
        _justification: &Option<Justification>,
    ) {
    }

    fn modify(_egraph: &mut EGraph<L, Self>, _id: Id) {}
}
