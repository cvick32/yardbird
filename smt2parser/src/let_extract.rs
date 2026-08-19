use std::collections::HashMap;

use crate::concrete::{Identifier, QualIdentifier, Symbol, Term};

#[derive(Clone, Debug, Default)]
pub struct LetExtract {
    pub scope: HashMap<Symbol, Term>,
}
impl LetExtract {
    /// Removes all lets and nested lets from `term`.
    pub fn substitute(term: Term) -> Term {
        let mut extractor = Self::default();
        extractor.substitute_scoped_symbols(term)
    }

    fn substitute_binder_body(&mut self, bound_symbols: &[Symbol], term: Term) -> Term {
        let shadowed = bound_symbols
            .iter()
            .map(|symbol| (symbol.clone(), self.scope.remove(symbol)))
            .collect::<Vec<_>>();
        let new_term = self.substitute_scoped_symbols(term);
        for (symbol, previous) in shadowed.into_iter().rev() {
            if let Some(previous) = previous {
                self.scope.insert(symbol, previous);
            }
        }
        new_term
    }

    fn substitute_scoped_symbols(&mut self, term: Term) -> Term {
        match term {
            Term::Constant(constant) => Term::Constant(constant),
            Term::QualIdentifier(q_id) => {
                let symbol: &Symbol = match &q_id {
                    QualIdentifier::Simple { identifier } => match identifier {
                        Identifier::Simple { symbol } => symbol,
                        Identifier::Indexed { symbol, indices: _ } => symbol,
                    },
                    QualIdentifier::Sorted {
                        identifier,
                        sort: _,
                    } => match identifier {
                        Identifier::Simple { symbol } => symbol,
                        Identifier::Indexed { symbol, indices: _ } => symbol,
                    },
                };
                if self.scope.contains_key(symbol) {
                    self.scope.get(symbol).unwrap().clone()
                } else {
                    Term::QualIdentifier(q_id)
                }
            }
            Term::Application {
                qual_identifier,
                arguments,
            } => {
                let new_arguments = arguments
                    .into_iter()
                    .map(|arg| self.substitute_scoped_symbols(arg))
                    .collect::<Vec<_>>();
                Term::Application {
                    qual_identifier,
                    arguments: new_arguments,
                }
            }
            Term::Lambda { vars, term } => {
                let bound_symbols = vars
                    .iter()
                    .map(|(symbol, _)| symbol.clone())
                    .collect::<Vec<_>>();
                let new_term = self.substitute_binder_body(&bound_symbols, *term);
                Term::Lambda {
                    vars,
                    term: Box::new(new_term),
                }
            }
            Term::Forall { vars, term } => {
                let bound_symbols = vars
                    .iter()
                    .map(|(symbol, _)| symbol.clone())
                    .collect::<Vec<_>>();
                let new_term = self.substitute_binder_body(&bound_symbols, *term);
                Term::Forall {
                    vars,
                    term: Box::new(new_term),
                }
            }
            Term::Exists { vars, term } => {
                let bound_symbols = vars
                    .iter()
                    .map(|(symbol, _)| symbol.clone())
                    .collect::<Vec<_>>();
                let new_term = self.substitute_binder_body(&bound_symbols, *term);
                Term::Exists {
                    vars,
                    term: Box::new(new_term),
                }
            }
            Term::Match { term, cases } => {
                let new_term = self.substitute_scoped_symbols(*term);
                let new_cases = cases
                    .into_iter()
                    .map(|(match_symbols, case)| {
                        (match_symbols, self.substitute_scoped_symbols(case))
                    })
                    .collect::<Vec<_>>();
                Term::Match {
                    term: Box::new(new_term),
                    cases: new_cases,
                }
            }
            Term::Attributes { term, attributes } => {
                let new_term = self.substitute_scoped_symbols(*term);
                Term::Attributes {
                    term: Box::new(new_term),
                    attributes,
                }
            }
            Term::Let { var_bindings, term } => {
                // SMT-LIB let bindings are simultaneous: every right-hand side
                // is evaluated in the incoming scope, before any sibling is bound.
                let substituted_bindings = var_bindings
                    .into_iter()
                    .map(|(var, term)| {
                        let var_term = self.substitute_scoped_symbols(term);
                        (var, var_term)
                    })
                    .collect::<Vec<_>>();
                let shadowed = substituted_bindings
                    .into_iter()
                    .map(|(var, var_term)| {
                        let previous = self.scope.insert(var.clone(), var_term);
                        (var, previous)
                    })
                    .collect::<Vec<_>>();
                let new_term = self.substitute_scoped_symbols(*term);
                for (var, previous) in shadowed.into_iter().rev() {
                    // Pop off the scope
                    if let Some(previous) = previous {
                        self.scope.insert(var, previous);
                    } else {
                        self.scope.remove(&var);
                    }
                }
                new_term
            }
        }
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
    macro_rules! create_let_test {
        ($test_name:ident, $test_term:literal, $should_be:literal) => {
            #[test]
            fn $test_name() {
                let term = get_term_from_assert_command_string($test_term);
                let new_term = LetExtract::substitute(term);
                assert!(
                    new_term.to_string() == $should_be,
                    "{} != {}",
                    new_term,
                    $should_be
                );
            }
        };
    }

    create_let_test!(test_no_let, b"(assert (let ((a 10)) 5))", "5");
    create_let_test!(
        test_one_variable,
        b"(assert (let ((a (<= 10 0))) (and a)))",
        "(and (<= 10 0))"
    );
    create_let_test!(
        test_two_variables,
        b"(assert (let ((a 10) (b 0)) (<= a b)))",
        "(<= 10 0)"
    );
    create_let_test!(
        test_variable_usage,
        b"(assert (let ((a 10) (b (+ a 10))) (<= a b)))",
        "(<= 10 (+ a 10))"
    );
    create_let_test!(test_actual_usage, b"(assert (and (let ((a!1 (not (not (= (Read_Int_Int c@1 Z@1) 99))))) (=> (and (>= i@1 N@1) (>= Z@1 100) (< Z@1 N@1)) (and a!1)))))", "(and (=> (and (>= i@1 N@1) (>= Z@1 100) (< Z@1 N@1)) (and (not (not (= (Read_Int_Int c@1 Z@1) 99))))))");
    create_let_test!(test_transition_use, b"(assert (and (let ((a!1 (= (Read_Int_Int c@0 i@0 (+ i@0 (Read_Int_Int a@0 i@0))) c@1)) (a!2 (= (Read_Int_Int c@0 i@0 (Read_Int_Int c@0 (- i@0 1))) c@1))) (and (=> (< i@0 100) a!1) (=> (not (< i@0 100)) a!2))) (< i@0 N@0) (= (+ i@0 1) i@1) (= a@0 a@1) (= N@0 N@1) (= Z@0 Z@1)))", "(and (and (=> (< i@0 100) (= (Read_Int_Int c@0 i@0 (+ i@0 (Read_Int_Int a@0 i@0))) c@1)) (=> (not (< i@0 100)) (= (Read_Int_Int c@0 i@0 (Read_Int_Int c@0 (- i@0 1))) c@1))) (< i@0 N@0) (= (+ i@0 1) i@1) (= a@0 a@1) (= N@0 N@1) (= Z@0 Z@1))");
    create_let_test!(test_double, b"(assert (let ((a!1 (and (not (and (< i N) (>= j 0))))) (a!2 (and (not (not (>= m n)))))) (=> a!1 a!2)))", "(=> (and (not (and (< i N) (>= j 0)))) (and (not (not (>= m n)))))");
    create_let_test!(
        test_nested,
        b"(assert (let ((a!1 2)) (let ((a!2 3)) (+ a!1 a!2))))",
        "(+ 2 3)"
    );
    create_let_test!(test_attribute, b"(assert (! (and (let ((a!1 (and (not (<= i (* 1 CC))) (>= Z 0) (< Z (* 5 CC)))) (a!2 (not (or (<= minval (select a Z)) (= (select a Z) 0))))) (=> a!1 (and (not a!2))))) :prop))", "(! (and (=> (and (not (<= i (* 1 CC))) (>= Z 0) (< Z (* 5 CC))) (and (not (not (or (<= minval (select a Z)) (= (select a Z) 0))))))) :prop)");
    create_let_test!(
        test_let_of_let,
        b"(assert (let ((a!1 (let ((a!2 3)) a!2))) a!1))",
        "3"
    );
    create_let_test!(
        test_nested_shadowing_restores_outer_binding,
        b"(assert (let ((a!1 true)) (and (let ((a!1 false)) (not a!1)) a!1)))",
        "(and (not false) true)"
    );
    create_let_test!(
        test_sibling_bindings_use_the_incoming_scope,
        b"(assert (let ((a 7)) (let ((a 10) (b (+ a 1))) (and (= a 10) (= b 8)))))",
        "(and (= 10 10) (= (+ 7 1) 8))"
    );
    create_let_test!(
        test_quantifier_binding_shadows_let_binding,
        b"(assert (let ((x 1)) (forall ((x Int)) (= x 1))))",
        "(forall ((x Int)) (= x 1))"
    );
    create_let_test!(
        test_lambda_binding_shadows_let_binding,
        b"(assert (let ((x 1)) (lambda ((x Int)) (+ x 1))))",
        "(lambda ((x Int)) (+ x 1))"
    );
}
