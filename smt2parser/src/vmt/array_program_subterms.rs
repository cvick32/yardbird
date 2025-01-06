use std::{collections::HashSet, fmt::Debug};

use crate::{
    concrete::{Constant, Keyword, QualIdentifier, SExpr, Sort, Symbol, Term},
    visitors::TermVisitor,
    Error,
};

use super::utils::is_boolean_connective;

#[derive(Clone, Debug, Default)]
pub struct ArrayProgramSubterms {
    pub subterms: HashSet<Term>,
}

impl TermVisitor<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort> for ArrayProgramSubterms {
    type T = Term;
    type E = Error;

    /// Add contstant term to subterms.
    fn visit_constant(&mut self, constant: Constant) -> Result<Self::T, Self::E> {
        self.subterms.insert(Term::Constant(constant.clone()));
        Ok(Term::Constant(constant))
    }

    fn visit_qual_identifier(
        &mut self,
        qual_identifier: QualIdentifier,
    ) -> Result<Self::T, Self::E> {
        let qi = Term::QualIdentifier(qual_identifier.clone());
        if !is_boolean_connective(&qual_identifier) && !is_array_function_name(&qual_identifier) {
            self.subterms.insert(qi.clone());
        }
        Ok(qi)
    }

    /// Add non-boolean connective function applications.
    fn visit_application(
        &mut self,
        qual_identifier: QualIdentifier,
        arguments: Vec<Self::T>,
    ) -> Result<Self::T, Self::E> {
        for argument in &arguments {
            let _ = argument.clone().accept_term_visitor(self);
        }
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
        let _ = term.clone().accept_term_visitor(self);
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
        let _ = term.clone().accept_term_visitor(self);
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
        let _ = term.clone().accept_term_visitor(self);
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
        let _ = term.clone().accept_term_visitor(self);
        Ok(Term::Attributes {
            term: Box::new(term),
            attributes,
        })
    }
}

fn is_array_function_name(qual_identifier: &QualIdentifier) -> bool {
    let name = qual_identifier.get_name();
    name.contains("Read") || name.contains("Write") || name.contains("ConstArr")
}
