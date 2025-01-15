use std::collections::HashSet;

use itertools::Itertools;

use crate::{
    concrete::{Constant, Keyword, QualIdentifier, SExpr, Sort, Symbol, Term},
    visitors::TermVisitor,
    Error,
};

#[derive(Clone, Default)]
pub struct ReadsAndWrites {
    /// Set of (Array, Index)
    pub reads_from: HashSet<(String, String)>,

    /// Set of (Array, Index, Value)
    pub writes_to: HashSet<(String, String, String)>,
}

impl ReadsAndWrites {
    /// Given an array, return all indicies written to
    pub fn write_array<A>(&self, array: A) -> impl Iterator<Item = String> + use<'_, A>
    where
        A: ToString,
    {
        let needle = array.to_string();
        self.writes_to
            .iter()
            .filter(move |(a, _i, _v)| &needle == a)
            .map(|(_a, i, _v)| i.to_string())
    }

    /// Given an array and index, return all values written to
    pub fn write_array_index<A, I>(
        &self,
        array: A,
        index: I,
    ) -> impl Iterator<Item = String> + use<'_, A, I>
    where
        A: ToString,
        I: ToString,
    {
        let array_needle = array.to_string();
        let index_needle = index.to_string();
        self.writes_to
            .iter()
            .filter(move |(a, i, _v)| &array_needle == a && &index_needle == i)
            .map(|(_, _, v)| v.to_string())
    }
}

impl std::fmt::Debug for ReadsAndWrites {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "ReadsAndWrites {{")?;

        write!(f, "  (select ")?;
        let read_args = self
            .reads_from
            .iter()
            .map(|(array, index)| format!("{array} {index}"))
            .join("\n          ");
        writeln!(f, "{read_args})")?;

        write!(f, "  (store ")?;
        let write_args = self
            .writes_to
            .iter()
            .map(|(array, index, value)| format!("{array} {index} {value}"))
            .join("\n         ");
        writeln!(f, "{write_args})")?;

        writeln!(f, "}}")?;

        Ok(())
    }
}

impl TermVisitor<Constant, QualIdentifier, Keyword, SExpr, Symbol, Sort> for ReadsAndWrites {
    type T = Term;
    type E = Error;

    fn visit_constant(&mut self, constant: Constant) -> Result<Self::T, Self::E> {
        Ok(Term::Constant(constant))
    }

    fn visit_qual_identifier(
        &mut self,
        qual_identifier: QualIdentifier,
    ) -> Result<Self::T, Self::E> {
        Ok(Term::QualIdentifier(qual_identifier))
    }

    fn visit_application(
        &mut self,
        qual_identifier: QualIdentifier,
        arguments: Vec<Self::T>,
    ) -> Result<Self::T, Self::E> {
        match (qual_identifier.to_string().as_str(), arguments.as_slice()) {
            ("Read-Int-Int" | "select", [array, index]) => {
                self.reads_from
                    .insert((array.to_string(), index.to_string()));
            }
            ("Write-Int-Int" | "store", [array, index, value]) => {
                self.writes_to
                    .insert((array.to_string(), index.to_string(), value.to_string()));
            }
            _ => (),
        }
        Ok(Term::Application {
            qual_identifier,
            arguments,
        })
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
