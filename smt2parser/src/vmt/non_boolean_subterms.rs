use std::{collections::HashSet, fmt::Debug};

use crate::{
    concrete::{Constant, Keyword, QualIdentifier, SExpr, Sort, Symbol, Term},
    visitors::TermVisitor,
    Error,
};

use super::utils::is_boolean_connective;

/// Use this visitor when you want to get all of the subterms of a given
/// term WITHOUT including function applications of boolean connectives.
/// For instance, if you have (or (= a@0 1) (a@0 2)) this will give you:
/// {a@0, 1, (= a@0 1), 2, (= a@0 2)}
/// One reason for not wanting boolean subterms is in yardbird, this information
/// will be latent in the egraph and we don't want to bog it down by adding
/// a bunch of equalities.
#[derive(Clone, Debug, Default)]
pub struct NonBooleanSubterms {
    pub subterms: HashSet<Term>,
}

impl TermVisitor<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort> for NonBooleanSubterms {
    type T = Term;
    type E = Error;

    /// Add constant term to subterms.
    fn visit_constant(&mut self, constant: Constant) -> Result<Self::T, Self::E> {
        self.subterms.insert(Term::Constant(constant.clone()));
        Ok(Term::Constant(constant))
    }

    /// Add variable names.
    fn visit_qual_identifier(
        &mut self,
        qual_identifier: QualIdentifier,
    ) -> Result<Self::T, Self::E> {
        let qi = Term::QualIdentifier(qual_identifier);
        self.subterms.insert(qi.clone());
        Ok(qi)
    }

    /// Add non-boolean connective function applications.
    fn visit_application(
        &mut self,
        qual_identifier: QualIdentifier,
        arguments: Vec<Self::T>,
    ) -> Result<Self::T, Self::E> {
        let app = Term::Application {
            qual_identifier: qual_identifier.clone(),
            arguments,
        };
        if !is_boolean_connective(&qual_identifier) {
            self.subterms.insert(app.clone());
        }
        Ok(app)
    }

    fn visit_let(
        &mut self,
        var_bindings: Vec<(Symbol, Self::T)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        Ok(Term::Let {
            var_bindings,
            term: Box::new(term),
        })
    }

    fn visit_forall(
        &mut self,
        vars: Vec<(Symbol, Sort)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        Ok(Term::Forall {
            vars,
            term: Box::new(term),
        })
    }

    fn visit_exists(
        &mut self,
        vars: Vec<(Symbol, Sort)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        Ok(Term::Exists {
            vars,
            term: Box::new(term),
        })
    }

    fn visit_match(
        &mut self,
        term: Self::T,
        cases: Vec<(Vec<Symbol>, Self::T)>,
    ) -> Result<Self::T, Self::E> {
        Ok(Term::Match {
            term: Box::new(term),
            cases,
        })
    }

    fn visit_attributes(
        &mut self,
        term: Self::T,
        attributes: Vec<(
            Keyword,
            crate::concrete::AttributeValue<Constant, Symbol, SExpr>,
        )>,
    ) -> Result<Self::T, Self::E> {
        Ok(Term::Attributes {
            term: Box::new(term),
            attributes,
        })
    }
}

mod test {

    #[allow(unused_imports)]
    use super::*;
    #[allow(unused_imports)]
    use crate::get_term_from_term_string;

    /// Have to pass a command-string to `test_term` because of CommandStream parsing.
    /// Easiest way to do this is to wrap whatever term you want to test inside of a
    /// call to `assert`.
    macro_rules! create_subterm_test {
        ($test_name:ident, $test_term:literal, $should_be:literal) => {
            #[test]
            fn $test_name() {
                let term = get_term_from_term_string($test_term);
                let mut subterms = NonBooleanSubterms::default();
                let _ = term.clone().accept_term_visitor(&mut subterms).unwrap();
                let mut string_subterms = subterms
                    .subterms
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<HashSet<_>>();
                println!("{:?}", string_subterms);
                for should_be_term in $should_be.split(",").into_iter() {
                    assert!(string_subterms.remove(&should_be_term.to_string()));
                }
                assert!(string_subterms.is_empty());
            }
        };
    }

    create_subterm_test!(test_simple, "(or (= a@0 1) (= a@0 2))", "a@0,1,2");

    create_subterm_test!(
        test_array_copy,
        "(and (= (store b i (select a i)) b_next) (< i n) (= (+ i 1) i_next) (= a a_next) (= n n_next) (= Z Z_next))",
        "b,i,a,n,Z,i_next,a_next,b_next,n_next,Z_next,(store b i (select a i)),(< i n),(select a i),(+ i 1),1"
    );
}
