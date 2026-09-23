//! Interpret Yardbird's typed array vocabulary using native solver arrays.
//! Binder lowering, matching, and instance installation retain their usual terms.
use crate::{
    solver::{SolverCheckResult, YardbirdSolver},
    utils::SolverStatistics,
    SolverBackend,
};
use smt2parser::{
    concrete::{Command, Identifier, QualIdentifier, Sort, Symbol, SyntaxBuilder, Term},
    rewriter::Rewriter,
    vmt::array_abstractor::string_to_sort,
};
use std::{
    collections::{BTreeMap, HashMap},
    time::Duration,
};

#[derive(Clone)]
enum ArrayOperation {
    Read,
    Write,
    Constant(Sort),
}

struct NativeArrays {
    sorts: HashMap<String, Sort>,
    operations: HashMap<String, ArrayOperation>,
}

impl NativeArrays {
    fn new(types: &[(String, String)]) -> Self {
        let mut sorts = HashMap::new();
        let mut operations = HashMap::new();
        for (index, value) in types {
            let sort = Sort::Parameterized {
                identifier: Identifier::Simple {
                    symbol: Symbol("Array".into()),
                },
                parameters: vec![string_to_sort(index), string_to_sort(value)],
            };
            sorts.insert(format!("Array_{index}_{value}"), sort.clone());
            operations.insert(format!("Read_{index}_{value}"), ArrayOperation::Read);
            operations.insert(format!("Write_{index}_{value}"), ArrayOperation::Write);
            operations.insert(
                format!("ConstArr_{index}_{value}"),
                ArrayOperation::Constant(sort),
            );
        }
        Self { sorts, operations }
    }

    fn rewriter(&self) -> NativeRewriter<'_> {
        NativeRewriter {
            encoding: self,
            builder: SyntaxBuilder,
        }
    }

    fn term(&self, term: &Term) -> anyhow::Result<Term> {
        term.clone()
            .accept(&mut self.rewriter())
            .map_err(|error| anyhow::anyhow!("{error}"))
    }

    fn terms(&self, terms: &[Term]) -> anyhow::Result<Vec<Term>> {
        terms.iter().map(|term| self.term(term)).collect()
    }

    fn sort(&self, sort: &Sort) -> anyhow::Result<Sort> {
        sort.clone()
            .accept(&mut self.rewriter())
            .map_err(|error| anyhow::anyhow!("{error}"))
    }

    fn command(&self, command: &Command) -> anyhow::Result<Option<Command>> {
        // These names now denote built-in sorts/operators, not additional UFs.
        match command {
            Command::DeclareSort { symbol, .. } if self.sorts.contains_key(&symbol.0) => {
                return Ok(None)
            }
            Command::DeclareFun { symbol, .. } if self.operations.contains_key(&symbol.0) => {
                return Ok(None)
            }
            _ => {}
        }
        command
            .clone()
            .accept(&mut self.rewriter())
            .map(Some)
            .map_err(|error| anyhow::anyhow!("{error}"))
    }
}

struct NativeRewriter<'a> {
    encoding: &'a NativeArrays,
    builder: SyntaxBuilder,
}

impl Rewriter for NativeRewriter<'_> {
    type V = SyntaxBuilder;
    type Error = smt2parser::concrete::Error;

    fn visitor(&mut self) -> &mut SyntaxBuilder {
        &mut self.builder
    }

    fn process_sort(&mut self, sort: Sort) -> Result<Sort, Self::Error> {
        if let Sort::Simple {
            identifier: Identifier::Simple { symbol },
        } = &sort
        {
            if let Some(native) = self.encoding.sorts.get(&symbol.0) {
                // Nested arrays can occur in either the index or value sort.
                return native.clone().accept(self);
            }
        }
        Ok(sort)
    }

    fn process_qual_identifier(
        &mut self,
        identifier: QualIdentifier,
    ) -> Result<QualIdentifier, Self::Error> {
        Ok(match self.encoding.operations.get(&identifier.get_name()) {
            Some(ArrayOperation::Read) => QualIdentifier::simple("select"),
            Some(ArrayOperation::Write) => QualIdentifier::simple("store"),
            Some(ArrayOperation::Constant(sort)) => QualIdentifier::Sorted {
                identifier: Identifier::Simple {
                    symbol: Symbol("const".into()),
                },
                sort: sort.clone().accept(self)?,
            },
            None => identifier,
        })
    }
}

pub(crate) struct NativeArraySolver {
    inner: Box<dyn YardbirdSolver>,
    encoding: NativeArrays,
}

impl NativeArraySolver {
    pub(crate) fn new(inner: Box<dyn YardbirdSolver>, types: &[(String, String)]) -> Self {
        Self {
            inner,
            encoding: NativeArrays::new(types),
        }
    }
}

impl YardbirdSolver for NativeArraySolver {
    fn backend(&self) -> SolverBackend {
        self.inner.backend()
    }
    fn solver_parameters(&self) -> BTreeMap<String, String> {
        self.inner.solver_parameters()
    }
    fn random_seeds(&self) -> BTreeMap<String, u64> {
        self.inner.random_seeds()
    }
    fn accept_command(&mut self, command: &Command) -> anyhow::Result<()> {
        if let Some(command) = self.encoding.command(command)? {
            self.inner.accept_command(&command)?;
        }
        Ok(())
    }
    fn create_variable(&mut self, symbol: &Symbol, sort: &Sort) -> anyhow::Result<()> {
        self.inner
            .create_variable(symbol, &self.encoding.sort(sort)?)
    }
    fn assert_term(&mut self, term: &Term) -> anyhow::Result<()> {
        self.inner.assert_term(&self.encoding.term(term)?)
    }
    fn assert_not_term(&mut self, term: &Term) -> anyhow::Result<()> {
        self.inner.assert_not_term(&self.encoding.term(term)?)
    }
    fn assert_terms_conjunctively(&mut self, terms: &[Term]) -> anyhow::Result<()> {
        self.inner
            .assert_terms_conjunctively(&self.encoding.terms(terms)?)
    }
    fn assert_tracked_term(&mut self, term: &Term, label: &str) -> anyhow::Result<()> {
        self.inner
            .assert_tracked_term(&self.encoding.term(term)?, label)
    }
    fn assert_instantiation_batch(&mut self, terms: &[Term]) -> anyhow::Result<()> {
        self.inner
            .assert_instantiation_batch(&self.encoding.terms(terms)?)
    }
    fn assert_tracked_instantiation(&mut self, label: &str, term: &Term) -> anyhow::Result<()> {
        self.inner
            .assert_tracked_instantiation(label, &self.encoding.term(term)?)
    }
    fn push(&mut self) {
        self.inner.push();
    }
    fn pop(&mut self, levels: u32) {
        self.inner.pop(levels);
    }
    fn check_sat(&mut self) -> SolverCheckResult {
        self.inner.check_sat()
    }
    fn check_sat_assuming(&mut self, assumptions: &[Term]) -> SolverCheckResult {
        self.inner.check_sat_assuming(
            &self
                .encoding
                .terms(assumptions)
                .expect("valid native array assumptions"),
        )
    }
    fn complete_check(&mut self) {
        self.inner.complete_check();
    }
    fn capture_model(&mut self, terms: &[Term]) -> anyhow::Result<()> {
        self.inner.capture_model(&self.encoding.terms(terms)?)
    }
    fn record_statistics(&mut self, elapsed: Duration) {
        self.inner.record_statistics(elapsed);
    }
    fn inspect_last_proof(&self) -> anyhow::Result<()> {
        self.inner.inspect_last_proof()
    }
    fn capture_unsat_core(&mut self) -> anyhow::Result<()> {
        self.inner.capture_unsat_core()
    }
    fn has_model(&self) -> bool {
        self.inner.has_model()
    }
    fn eval_to_string(&self, term: &Term) -> anyhow::Result<String> {
        self.inner.eval_to_string(&self.encoding.term(term)?)
    }
    fn model_to_string(&self) -> anyhow::Result<String> {
        self.inner.model_to_string()
    }
    fn get_solver_statistics(&self) -> SolverStatistics {
        self.inner.get_solver_statistics()
    }
    fn statistics_ref(&self) -> &SolverStatistics {
        self.inner.statistics_ref()
    }
    fn get_reason_unknown(&self) -> Option<String> {
        self.inner.get_reason_unknown()
    }
    fn get_unsat_core(&self) -> anyhow::Result<Vec<String>> {
        self.inner.get_unsat_core()
    }
    fn to_smt2_string(&self) -> anyhow::Result<String> {
        self.inner.to_smt2_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use smt2parser::CommandStream;

    #[test]
    fn translates_nested_array_sorts_and_constants_without_parsing_type_names() {
        let encoding = NativeArrays::new(&[
            ("node_with_underscores".into(), "Array_BitVec8_Bool".into()),
            ("BitVec8".into(), "Bool".into()),
            ("Array_BitVec8_Bool".into(), "Int".into()),
        ]);
        assert_eq!(
            encoding
                .sort(&string_to_sort(
                    "Array_node_with_underscores_Array_BitVec8_Bool"
                ))
                .unwrap()
                .to_string(),
            "(Array node_with_underscores (Array (_ BitVec 8) Bool))"
        );
        assert_eq!(
            encoding
                .sort(&string_to_sort("Array_Array_BitVec8_Bool_Int"))
                .unwrap()
                .to_string(),
            "(Array (Array (_ BitVec 8) Bool) Int)"
        );
        let term: Term = "(Read_BitVec8_Bool (Read_node_with_underscores_Array_BitVec8_Bool (Write_node_with_underscores_Array_BitVec8_Bool a n (ConstArr_BitVec8_Bool true)) n) #x00)".parse().unwrap();
        assert_eq!(
            encoding.term(&term).unwrap().to_string(),
            "(select (select (store a n ((as const (Array (_ BitVec 8) Bool)) true)) n) #x00)"
        );
        let function = CommandStream::new(
            "(declare-fun binder (Array_node_with_underscores_Array_BitVec8_Bool) Bool)".as_bytes(),
            SyntaxBuilder,
            None,
        )
        .next()
        .unwrap()
        .unwrap();
        assert_eq!(
            encoding.command(&function).unwrap().unwrap().to_string(),
            "(declare-fun binder ((Array node_with_underscores (Array (_ BitVec 8) Bool))) Bool)"
        );
        let unrelated: Term = "(Read_other_type a n)".parse().unwrap();
        assert_eq!(encoding.term(&unrelated).unwrap(), unrelated);
    }
}
