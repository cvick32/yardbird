use egg::*;

define_language! {
    pub enum ArrayLanguage {
        Num(i64),
        "K" = ConstArr([Id; 1]),
        "Write" = Write([Id; 3]),
        "Read" = Read([Id; 2]),
        Symbol(Symbol),
    }
}

/// Trait for saturating an egraph with the array axioms. This hides the details of
/// needing to create a runner every time you want to saturate a set of rules on an egraph.
pub trait Saturate {
    fn saturate(&mut self);
}

impl Saturate for EGraph<ArrayLanguage, ()> {
    fn saturate(&mut self) {
        let egraph = std::mem::take(self);
        let runner = Runner::default().with_egraph(egraph).run(&array_axioms());
        *self = runner.egraph;
    }
}

fn array_axioms() -> Vec<Rewrite<ArrayLanguage, ()>> {
    vec![
        rewrite!("constant-array"; "(Read (K ?a) ?b)" => "?a"),
        rewrite!("read-after-write"; "(Read (Write ?a ?idx ?val) ?idx)" => "?val"),
        rewrite!("write-does-not-overwrite"; "(Read (Write ?a ?idx ?val) ?c)" => "(Read ?a ?c)" if not_equal("?idx", "?c")),
    ]
}

fn not_equal(
    index_0: &'static str,
    index_1: &'static str,
) -> impl Fn(&mut EGraph<ArrayLanguage, ()>, Id, &Subst) -> bool {
    let var_0 = index_0.parse().unwrap();
    let var_1 = index_1.parse().unwrap();

    move |egraph, _, subst| egraph.find(subst[var_0]) != egraph.find(subst[var_1])
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_conditional_axioms0() {
        let expr: RecExpr<ArrayLanguage> = "(Read (Write A 0 0) 1)".parse().unwrap();
        let runner = Runner::default().with_expr(&expr).run(&array_axioms());

        let gold: RecExpr<ArrayLanguage> = "(Read A 1)".parse().unwrap();
        assert!(runner.egraph.lookup_expr(&gold).is_some())
    }

    #[test]
    fn test_conditional_axioms1() {
        let expr: RecExpr<ArrayLanguage> = "(Read (Write A 0 0) 0)".parse().unwrap();
        let runner = Runner::default().with_expr(&expr).run(&array_axioms());

        let gold: RecExpr<ArrayLanguage> = "(Read A 0)".parse().unwrap();
        assert!(runner.egraph.lookup_expr(&gold).is_none())
    }

    /// Construct a sample model that is invalid according to the array axioms, and find
    /// an instantiation of an axiom that proves this.
    ///
    /// Let's take this sample model that is obviously invalid. We'll construct this by
    /// instantiating the terms `(Read (K 0) 0)` and `1` and unioning them in the
    /// egraph.
    ///
    /// ```
    /// (Read (K 0) 0) = 1
    /// ```
    ///
    /// Then I think that we want to get out an axiom instantiation that looks like
    /// `(Read (K 0) 0) = 0` because that will rule out that union being possible.
    #[test]
    fn invalid_const_array() {
        let mut egraph: EGraph<ArrayLanguage, _> = EGraph::new(()).with_explanations_enabled();

        let read_term: RecExpr<ArrayLanguage> = "(Read (K 0) 0)".parse().unwrap();
        let one_term: RecExpr<ArrayLanguage> = "1".parse().unwrap();

        let read_handle = egraph.add_expr(&read_term);
        let one_handle = egraph.add_expr(&one_term);

        egraph.union(read_handle, one_handle);
        egraph.saturate();

        let mut explanation =
            egraph.explain_equivalence(&"0".parse().unwrap(), &"1".parse().unwrap());

        // println!("{:#?}", explanation.explanation_trees);
        println!("{}", explanation.get_flat_string());

        assert!(false);
    }
}
