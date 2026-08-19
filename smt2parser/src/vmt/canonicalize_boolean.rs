use crate::{
    concrete::{Constant, Keyword, QualIdentifier, SExpr, Sort, Symbol, Term},
    visitors::TermVisitor,
    Error,
};

#[derive(Clone, Debug, Default)]
/// SMTInterpol doesn't accept `and` terms with non-2 arity. For instance, neither (and b@0) nor
/// (and b@1 b@1 b@1) will compile. This visitor rewrites `and` and `or` terms to use only arity-2.
pub struct CanonicalizeBooleanFunctions {}

impl TermVisitor<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort>
    for CanonicalizeBooleanFunctions
{
    type T = Term;
    type E = Error;

    fn visit_application(
        &mut self,
        qual_identifier: QualIdentifier,
        arguments: Vec<Self::T>,
    ) -> Result<Self::T, Self::E> {
        let function_name = qual_identifier.get_name();
        if function_name == "and" || function_name == "or" {
            if arguments.len() == 1 {
                Ok(arguments[0].clone())
            } else if arguments.len() > 2 {
                let outer_and = &arguments[0];

                let inner_and_arguments = Term::Application {
                    qual_identifier: qual_identifier.clone(),
                    arguments: arguments.clone().split_off(1),
                };
                let new_inner = inner_and_arguments.accept_term_visitor(self).unwrap();
                Ok(Term::Application {
                    qual_identifier: qual_identifier.clone(),
                    arguments: vec![outer_and.clone(), new_inner],
                })
            } else {
                Ok(Term::Application {
                    qual_identifier: qual_identifier.clone(),
                    arguments,
                })
            }
        } else {
            let new_args = arguments
                .iter()
                .map(|arg| arg.clone().accept_term_visitor(self).unwrap())
                .collect();
            Ok(Term::Application {
                qual_identifier: qual_identifier.clone(),
                arguments: new_args,
            })
        }
    }

    fn visit_constant(&mut self, constant: Constant) -> Result<Self::T, Self::E> {
        Ok(Term::Constant(constant))
    }

    fn visit_qual_identifier(
        &mut self,
        qual_identifier: QualIdentifier,
    ) -> Result<Self::T, Self::E> {
        Ok(Term::QualIdentifier(qual_identifier))
    }

    fn visit_let(
        &mut self,
        var_bindings: Vec<(Symbol, Self::T)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        let new_bindings = var_bindings
            .iter()
            .map(|(symbol, bound_term)| {
                (
                    symbol.clone(),
                    bound_term.clone().accept_term_visitor(self).unwrap(),
                )
            })
            .collect();
        Ok(Term::Let {
            var_bindings: new_bindings,
            term: Box::new(term.accept_term_visitor(self).unwrap()),
        })
    }

    fn visit_lambda(
        &mut self,
        vars: Vec<(Symbol, Sort)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        Ok(Term::Lambda {
            vars,
            term: Box::new(term.accept_term_visitor(self).unwrap()),
        })
    }

    fn visit_forall(
        &mut self,
        vars: Vec<(Symbol, Sort)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        Ok(Term::Forall {
            vars,
            term: Box::new(term.accept_term_visitor(self).unwrap()),
        })
    }

    fn visit_exists(
        &mut self,
        vars: Vec<(Symbol, Sort)>,
        term: Self::T,
    ) -> Result<Self::T, Self::E> {
        Ok(Term::Exists {
            vars,
            term: Box::new(term.accept_term_visitor(self).unwrap()),
        })
    }

    fn visit_match(
        &mut self,
        term: Self::T,
        cases: Vec<(Vec<Symbol>, Self::T)>,
    ) -> Result<Self::T, Self::E> {
        Ok(Term::Match {
            term: Box::new(term.accept_term_visitor(self).unwrap()),
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
            term: Box::new(term.accept_term_visitor(self).unwrap()),
            attributes,
        })
    }
}

mod test {

    #[allow(unused_imports)]
    use super::*;
    #[allow(unused_imports)]
    use crate::get_term_from_assert_command_string;

    /// Have to pass a command-string to `test_term` because of CommandStream parsing.
    /// Easiest way to do this is to wrap whatever term you want to test inside of a
    /// call to `assert`.
    macro_rules! create_smt_interpol_test {
        ($test_name:ident, $test_term:literal, $should_be:literal) => {
            #[test]
            fn $test_name() {
                let term = get_term_from_assert_command_string($test_term);
                let mut let_extract = CanonicalizeBooleanFunctions::default();
                let new_term = term.clone().accept_term_visitor(&mut let_extract).unwrap();
                assert!(
                    new_term.to_string() == $should_be,
                    "{} != {}",
                    new_term,
                    $should_be
                );
            }
        };
    }

    create_smt_interpol_test!(test_no_and, b"(assert (= a 1))", "(= a 1)");
    create_smt_interpol_test!(test_one_and, b"(assert (and (= a 1)))", "(= a 1)");
    create_smt_interpol_test!(test_one_or, b"(assert (or (= a 1)))", "(= a 1)");
    create_smt_interpol_test!(test_two_and, b"(assert (and a b))", "(and a b)");
    create_smt_interpol_test!(test_two_or, b"(assert (or a b))", "(or a b)");
    create_smt_interpol_test!(test_three_and, b"(assert (and a b c))", "(and a (and b c))");
    create_smt_interpol_test!(test_three_or, b"(assert (or a b c))", "(or a (or b c))");
    create_smt_interpol_test!(
        test_four_and,
        b"(assert (and a b c d))",
        "(and a (and b (and c d)))"
    );
    create_smt_interpol_test!(
        test_simple_nested_and,
        b"(assert (and a b (and c d)))",
        "(and a (and b (and c d)))"
    );
    create_smt_interpol_test!(
        test_nested_and1,
        b"(assert (and a b (and c (and d e f))))",
        "(and a (and b (and c (and d (and e f)))))"
    );
    create_smt_interpol_test!(
        test_nested_and2,
        b"(assert (and a b (and c (and d e f))))",
        "(and a (and b (and c (and d (and e f)))))"
    );
    create_smt_interpol_test!(
        test_nested_and3,
        b"(assert (and (and a b c) (and d e f)))",
        "(and (and a (and b c)) (and d (and e f)))"
    );
    create_smt_interpol_test!(
        test_or_over_and,
        b"(assert (or (and a b c) (and d e f)))",
        "(or (and a (and b c)) (and d (and e f)))"
    );
    create_smt_interpol_test!(
        test_and_in_let,
        b"(assert (not (let ((a!1 (and a b c))) (=> (and d e f) (and a!1)))))",
        "(not (let ((a!1 (and a (and b c)))) (=> (and d (and e f)) a!1)))"
    );
}
