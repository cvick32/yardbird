use egg::{Analysis, DidMerge, EGraph, Id, Justification};

use crate::theories::array_axioms::ArrayLanguage;

#[derive(Default)]
pub struct SaturationInequalities;

impl Analysis<ArrayLanguage> for SaturationInequalities {
    type Data = bool;
    fn make(_egraph: &EGraph<ArrayLanguage, Self>, _enode: &ArrayLanguage) -> Self::Data {
        false
    }
    fn merge(&mut self, a: &mut Self::Data, _b: Self::Data) -> DidMerge {
        *a = true;
        DidMerge(false, true)
    }

    fn pre_union(
        _egraph: &EGraph<ArrayLanguage, Self>,
        _id1: Id,
        _id2: Id,
        _justification: &Option<Justification>,
    ) {
    }

    fn modify(_egraph: &mut EGraph<ArrayLanguage, Self>, _id: Id) {}
}
