use std::{collections::HashMap, time::Instant};

use cvc5::{Kind, Solver, Sort, Term, TermManager};
use smt2parser::concrete::{
    AttributeValue, Command, Constant, Identifier, QualIdentifier, Sort as SmtSort, Symbol,
    Term as SmtTerm,
};
use smt2parser::visitors::Index;

use crate::{
    solver::{SolverCheckResult, YardbirdSolver},
    utils::SolverStatistics,
    SolverBackend,
};

pub struct Cvc5SolverBackend {
    tm: &'static TermManager,
    solver: Solver<'static>,
    sorts: HashMap<String, Sort<'static>>,
    terms: HashMap<String, Term<'static>>,
    tracked_labels: Vec<(String, Term<'static>)>,
    solver_statistics: SolverStatistics,
    last_result: Option<SolverCheckResult>,
}

impl Cvc5SolverBackend {
    pub(crate) fn new(logic: &str) -> Self {
        let tm: &'static TermManager = Box::leak(Box::new(TermManager::new()));
        let mut solver = Solver::new(tm);
        solver.set_option("produce-models", "true");
        solver.set_option("produce-unsat-cores", "true");
        solver.set_option("produce-unsat-assumptions", "true");
        solver.set_option("incremental", "true");
        solver.set_option("arrays-exp", "true");
        solver.set_logic(logic);

        Self {
            tm,
            solver,
            sorts: HashMap::new(),
            terms: HashMap::new(),
            tracked_labels: vec![],
            solver_statistics: SolverStatistics::new(),
            last_result: None,
        }
    }

    fn convert_sort(&mut self, sort: &SmtSort) -> anyhow::Result<Sort<'static>> {
        match sort {
            SmtSort::Simple { identifier } => self.convert_simple_sort(identifier),
            SmtSort::Parameterized {
                identifier,
                parameters,
            } if identifier_name(identifier) == "Array" && parameters.len() == 2 => {
                let index_sort = self.convert_sort(&parameters[0])?;
                let element_sort = self.convert_sort(&parameters[1])?;
                Ok(self.tm.mk_array_sort(index_sort, element_sort))
            }
            SmtSort::Parameterized {
                identifier,
                parameters,
            } => {
                anyhow::bail!(
                    "unsupported CVC5 parameterized sort: {} with {} parameter(s)",
                    identifier_name(identifier),
                    parameters.len()
                )
            }
        }
    }

    fn convert_sort_ref(&self, sort: &SmtSort) -> anyhow::Result<Sort<'static>> {
        match sort {
            SmtSort::Simple { identifier } => self.convert_simple_sort_ref(identifier),
            SmtSort::Parameterized {
                identifier,
                parameters,
            } if identifier_name(identifier) == "Array" && parameters.len() == 2 => {
                let index_sort = self.convert_sort_ref(&parameters[0])?;
                let element_sort = self.convert_sort_ref(&parameters[1])?;
                Ok(self.tm.mk_array_sort(index_sort, element_sort))
            }
            SmtSort::Parameterized {
                identifier,
                parameters,
            } => {
                anyhow::bail!(
                    "unsupported CVC5 parameterized sort: {} with {} parameter(s)",
                    identifier_name(identifier),
                    parameters.len()
                )
            }
        }
    }

    fn convert_simple_sort(&mut self, identifier: &Identifier) -> anyhow::Result<Sort<'static>> {
        match identifier {
            Identifier::Simple { symbol } => match symbol.0.as_str() {
                "Bool" => Ok(self.tm.boolean_sort()),
                "Int" => Ok(self.tm.integer_sort()),
                name => {
                    if let Some(sort) = self.sorts.get(name) {
                        Ok(sort.clone())
                    } else {
                        let sort = self.solver.declare_sort(name, 0);
                        self.sorts.insert(name.to_string(), sort.clone());
                        Ok(sort)
                    }
                }
            },
            Identifier::Indexed { symbol, indices } if symbol.0 == "BitVec" => {
                let width = single_numeral_index("BitVec sort", indices)?;
                Ok(self.tm.mk_bv_sort(width))
            }
            Identifier::Indexed { symbol, .. } => {
                anyhow::bail!("unsupported CVC5 indexed sort: {}", symbol.0)
            }
        }
    }

    fn convert_simple_sort_ref(&self, identifier: &Identifier) -> anyhow::Result<Sort<'static>> {
        match identifier {
            Identifier::Simple { symbol } => match symbol.0.as_str() {
                "Bool" => Ok(self.tm.boolean_sort()),
                "Int" => Ok(self.tm.integer_sort()),
                name => Ok(self
                    .sorts
                    .get(name)
                    .cloned()
                    .unwrap_or_else(|| self.tm.mk_uninterpreted_sort(name))),
            },
            Identifier::Indexed { symbol, indices } if symbol.0 == "BitVec" => {
                let width = single_numeral_index("BitVec sort", indices)?;
                Ok(self.tm.mk_bv_sort(width))
            }
            Identifier::Indexed { symbol, .. } => {
                anyhow::bail!("unsupported CVC5 indexed sort: {}", symbol.0)
            }
        }
    }

    fn convert_term(&self, term: &SmtTerm) -> anyhow::Result<Term<'static>> {
        match term {
            SmtTerm::Constant(constant) => self.convert_constant(constant),
            SmtTerm::QualIdentifier(qual_identifier) => {
                self.convert_qual_identifier(qual_identifier)
            }
            SmtTerm::Application {
                qual_identifier,
                arguments,
            } => self.convert_application(qual_identifier, arguments),
            SmtTerm::Forall { .. } => {
                anyhow::bail!("CVC5 forall conversion requires assertion context")
            }
            SmtTerm::Let { .. }
            | SmtTerm::Exists { .. }
            | SmtTerm::Match { .. }
            | SmtTerm::Attributes { .. } => {
                anyhow::bail!("unsupported CVC5 term: {term}")
            }
        }
    }

    fn convert_assertion_term(&mut self, term: &SmtTerm) -> anyhow::Result<Term<'static>> {
        match term {
            SmtTerm::Forall { vars, term } => self.convert_forall(vars, term),
            SmtTerm::Constant(constant) => self.convert_constant(constant),
            SmtTerm::QualIdentifier(qual_identifier) => {
                self.convert_qual_identifier(qual_identifier)
            }
            SmtTerm::Application {
                qual_identifier,
                arguments,
            } => {
                let args = arguments
                    .iter()
                    .map(|term| self.convert_assertion_term(term))
                    .collect::<anyhow::Result<Vec<_>>>()?;
                self.make_application(qual_identifier, args)
            }
            SmtTerm::Let { .. }
            | SmtTerm::Exists { .. }
            | SmtTerm::Match { .. }
            | SmtTerm::Attributes { .. } => {
                anyhow::bail!("unsupported CVC5 assertion term: {term}")
            }
        }
    }

    fn convert_forall(
        &mut self,
        vars: &[(Symbol, SmtSort)],
        term: &SmtTerm,
    ) -> anyhow::Result<Term<'static>> {
        let mut bound_vars = Vec::with_capacity(vars.len());
        let mut shadowed_terms = Vec::with_capacity(vars.len());

        for (symbol, sort) in vars {
            let sort = self.convert_sort(sort)?;
            let var = self.tm.mk_var(sort, &symbol.0);
            let previous = self.terms.insert(symbol.0.clone(), var.clone());
            shadowed_terms.push((symbol.0.clone(), previous));
            bound_vars.push(var);
        }

        let body_result = self.convert_assertion_term(term);

        for (name, previous) in shadowed_terms.into_iter().rev() {
            if let Some(previous) = previous {
                self.terms.insert(name, previous);
            } else {
                self.terms.remove(&name);
            }
        }

        let body = body_result?;
        let variable_list = self.tm.mk_term(Kind::VariableList, &bound_vars);
        Ok(self.tm.mk_term(Kind::Forall, &[variable_list, body]))
    }

    fn convert_constant(&self, constant: &Constant) -> anyhow::Result<Term<'static>> {
        match constant {
            Constant::Numeral(value) => Ok(self.tm.mk_integer_from_str(&value.to_string())),
            Constant::Decimal(value) => Ok(self.tm.mk_real_from_str(&value.to_string())),
            Constant::Hexadecimal(hex_bytes) => {
                let bit_width = (hex_bytes.len() * 4) as u32;
                let hex_value = hex_bytes
                    .iter()
                    .map(|digit| format!("{digit:x}"))
                    .collect::<String>();
                Ok(self.tm.mk_bv_from_str(bit_width, &hex_value, 16))
            }
            Constant::Binary(_) => {
                anyhow::bail!("CVC5 binary constants are not part of the current Z3 parity set")
            }
            Constant::String(_) => anyhow::bail!("CVC5 string constants are unsupported"),
        }
    }

    fn convert_qual_identifier(
        &self,
        qual_identifier: &QualIdentifier,
    ) -> anyhow::Result<Term<'static>> {
        match qual_identifier {
            QualIdentifier::Simple {
                identifier: Identifier::Indexed { symbol, indices },
            } if symbol.0.starts_with("bv") => self.convert_indexed_bv_literal(&symbol.0, indices),
            _ => {
                let name = qual_identifier.get_name();
                match name.as_str() {
                    "true" => Ok(self.tm.mk_true()),
                    "false" => Ok(self.tm.mk_false()),
                    _ => self
                        .terms
                        .get(&name)
                        .cloned()
                        .ok_or_else(|| anyhow::anyhow!("unknown CVC5 term symbol: {name}")),
                }
            }
        }
    }

    fn convert_application(
        &self,
        qual_identifier: &QualIdentifier,
        arguments: &[SmtTerm],
    ) -> anyhow::Result<Term<'static>> {
        let args = arguments
            .iter()
            .map(|term| self.convert_term(term))
            .collect::<anyhow::Result<Vec<_>>>()?;

        self.make_application(qual_identifier, args)
    }

    fn make_application(
        &self,
        qual_identifier: &QualIdentifier,
        args: Vec<Term<'static>>,
    ) -> anyhow::Result<Term<'static>> {
        if let Some((symbol, indices)) = indexed_identifier_parts(qual_identifier) {
            if symbol.starts_with("bv") {
                return self.convert_indexed_bv_literal(symbol, indices);
            }
            return self.make_indexed_application(symbol, indices, args);
        }

        let name = qual_identifier.get_name();

        if name == "const" {
            return self.make_const_array(qual_identifier, args);
        }

        match name.as_str() {
            "=" if args.len() == 2 => Ok(self.tm.mk_term(Kind::Equal, &args)),
            "and" => Ok(self.tm.mk_term(Kind::And, &args)),
            "or" => Ok(self.tm.mk_term(Kind::Or, &args)),
            "not" if args.len() == 1 => Ok(self.tm.mk_term(Kind::Not, &args)),
            "=>" if args.len() == 2 => Ok(self.tm.mk_term(Kind::Implies, &args)),
            "ite" if args.len() == 3 => Ok(self.tm.mk_term(Kind::Ite, &args)),
            "+" => Ok(self.tm.mk_term(Kind::Add, &args)),
            "-" if args.len() == 1 => Ok(self.tm.mk_term(Kind::Neg, &args)),
            "-" => Ok(self.tm.mk_term(Kind::Sub, &args)),
            "*" => Ok(self.tm.mk_term(Kind::Mult, &args)),
            "/" if args.len() == 2 => Ok(self.tm.mk_term(Kind::IntsDivision, &args)),
            "mod" if args.len() == 2 => Ok(self.tm.mk_term(Kind::IntsModulus, &args)),
            ">" if args.len() == 2 => Ok(self.tm.mk_term(Kind::Gt, &args)),
            ">=" if args.len() == 2 => Ok(self.tm.mk_term(Kind::Geq, &args)),
            "<" if args.len() == 2 => Ok(self.tm.mk_term(Kind::Lt, &args)),
            "<=" if args.len() == 2 => Ok(self.tm.mk_term(Kind::Leq, &args)),
            "select" if args.len() == 2 => Ok(self.tm.mk_term(Kind::Select, &args)),
            "store" if args.len() == 3 => Ok(self.tm.mk_term(Kind::Store, &args)),
            "concat" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorConcat, &args)),
            "bvule" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorUle, &args)),
            "bvult" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorUlt, &args)),
            "bvuge" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorUge, &args)),
            "bvugt" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorUgt, &args)),
            "bvsle" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorSle, &args)),
            "bvslt" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorSlt, &args)),
            "bvsge" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorSge, &args)),
            "bvsgt" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorSgt, &args)),
            "bvadd" if args.len() >= 2 => {
                self.make_left_associative_bv_term(Kind::BitvectorAdd, args)
            }
            "bvsub" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorSub, &args)),
            "bvmul" if args.len() >= 2 => {
                self.make_left_associative_bv_term(Kind::BitvectorMult, args)
            }
            "bvand" if args.len() >= 2 => {
                self.make_left_associative_bv_term(Kind::BitvectorAnd, args)
            }
            "bvor" if args.len() >= 2 => {
                self.make_left_associative_bv_term(Kind::BitvectorOr, args)
            }
            "bvxor" if args.len() >= 2 => {
                self.make_left_associative_bv_term(Kind::BitvectorXor, args)
            }
            "bvnot" if args.len() == 1 => Ok(self.tm.mk_term(Kind::BitvectorNot, &args)),
            "bvneg" if args.len() == 1 => Ok(self.tm.mk_term(Kind::BitvectorNeg, &args)),
            "bvlshr" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorLshr, &args)),
            "bvashr" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorAshr, &args)),
            "bvshl" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorShl, &args)),
            "bvudiv" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorUdiv, &args)),
            "bvurem" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorUrem, &args)),
            "bvsdiv" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorSdiv, &args)),
            "bvsrem" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorSrem, &args)),
            "bvsmod" if args.len() == 2 => Ok(self.tm.mk_term(Kind::BitvectorSmod, &args)),
            _ => {
                if let Some(function) = self.terms.get(&name) {
                    let children = std::iter::once(function.clone())
                        .chain(args)
                        .collect::<Vec<_>>();
                    Ok(self.tm.mk_term(Kind::ApplyUf, &children))
                } else {
                    anyhow::bail!("unsupported CVC5 application: {name}")
                }
            }
        }
    }

    fn make_const_array(
        &self,
        qual_identifier: &QualIdentifier,
        args: Vec<Term<'static>>,
    ) -> anyhow::Result<Term<'static>> {
        if args.len() != 1 {
            anyhow::bail!("CVC5 const array expects one value argument");
        }

        let QualIdentifier::Sorted { sort, .. } = qual_identifier else {
            anyhow::bail!("CVC5 const array requires a sorted `(as const Sort)` identifier");
        };

        let array_sort = self.convert_sort_ref(sort)?;
        Ok(self.tm.mk_const_array(array_sort, args[0].clone()))
    }

    fn make_left_associative_bv_term(
        &self,
        kind: Kind,
        args: Vec<Term<'static>>,
    ) -> anyhow::Result<Term<'static>> {
        let mut terms = args.into_iter();
        let Some(mut result) = terms.next() else {
            anyhow::bail!("bitvector operation requires at least one argument");
        };

        for term in terms {
            result = self.tm.mk_term(kind, &[result, term]);
        }

        Ok(result)
    }

    fn make_indexed_application(
        &self,
        function_name: &str,
        indices: &[Index],
        args: Vec<Term<'static>>,
    ) -> anyhow::Result<Term<'static>> {
        match function_name {
            "extract" if args.len() == 1 && indices.len() == 2 => {
                let high = numeral_index("extract high", &indices[0])?;
                let low = numeral_index("extract low", &indices[1])?;
                let op = self.tm.mk_op(Kind::BitvectorExtract, &[high, low]);
                Ok(self.tm.mk_term_from_op(op, &args))
            }
            "zero_extend" if args.len() == 1 && indices.len() == 1 => {
                let extension = numeral_index("zero_extend", &indices[0])?;
                let op = self.tm.mk_op(Kind::BitvectorZeroExtend, &[extension]);
                Ok(self.tm.mk_term_from_op(op, &args))
            }
            "sign_extend" if args.len() == 1 && indices.len() == 1 => {
                let extension = numeral_index("sign_extend", &indices[0])?;
                let op = self.tm.mk_op(Kind::BitvectorSignExtend, &[extension]);
                Ok(self.tm.mk_term_from_op(op, &args))
            }
            _ => anyhow::bail!(
                "unsupported CVC5 indexed application: (_ {function_name} {}) with {} argument(s)",
                indices
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" "),
                args.len()
            ),
        }
    }

    fn convert_indexed_bv_literal(
        &self,
        symbol: &str,
        indices: &[Index],
    ) -> anyhow::Result<Term<'static>> {
        let value = symbol
            .strip_prefix("bv")
            .ok_or_else(|| anyhow::anyhow!("bitvector literal must start with bv: {symbol}"))?;
        let width = single_numeral_index("bitvector literal", indices)?;
        Ok(self.tm.mk_bv_from_str(width, value, 10))
    }
}

impl YardbirdSolver for Cvc5SolverBackend {
    fn backend(&self) -> SolverBackend {
        SolverBackend::Cvc5
    }

    fn accept_command(&mut self, command: &Command) -> anyhow::Result<()> {
        match command {
            Command::DeclareSort { symbol, arity } => {
                if *arity != 0u32.into() {
                    anyhow::bail!("CVC5 backend only supports zero-arity declare-sort: {symbol}");
                }
                let sort = self.solver.declare_sort(&symbol.0, 0);
                self.sorts.insert(symbol.0.clone(), sort);
                Ok(())
            }
            Command::DeclareConst { symbol, sort } => {
                let cvc5_sort = self.convert_sort(sort)?;
                let term = self.solver.declare_fun(&symbol.0, &[], cvc5_sort);
                self.terms.insert(symbol.0.clone(), term);
                Ok(())
            }
            Command::DeclareFun {
                symbol,
                parameters,
                sort,
            } => {
                let domain = parameters
                    .iter()
                    .map(|sort| self.convert_sort(sort))
                    .collect::<anyhow::Result<Vec<_>>>()?;
                let codomain = self.convert_sort(sort)?;
                let term = self.solver.declare_fun(&symbol.0, &domain, codomain);
                self.terms.insert(symbol.0.clone(), term);
                Ok(())
            }
            Command::DefineFun { sig, term } if sig.parameters.is_empty() => {
                let value = self.convert_assertion_term(term)?;
                self.terms.insert(sig.name.0.clone(), value);
                Ok(())
            }
            Command::SetOption { keyword, value } => {
                if let Some(value) = attribute_value_to_option_string(value) {
                    self.solver.set_option(&keyword.0, &value);
                }
                Ok(())
            }
            Command::SetLogic { symbol } => {
                self.solver.set_logic(&symbol.0);
                Ok(())
            }
            Command::DefineFun { sig, .. } => {
                anyhow::bail!(
                    "CVC5 backend only supports zero-argument define-fun: {}",
                    sig.name.0
                )
            }
            _ => Ok(()),
        }
    }

    fn create_variable(&mut self, symbol: &Symbol, sort: &SmtSort) -> anyhow::Result<()> {
        let cvc5_sort = self.convert_sort(sort)?;
        let term = self.tm.mk_var(cvc5_sort, &symbol.0);
        self.terms.insert(symbol.0.clone(), term);
        Ok(())
    }

    fn assert_term(&mut self, term: &SmtTerm) -> anyhow::Result<()> {
        let cvc5_term = self.convert_assertion_term(term)?;
        self.solver.assert_formula(cvc5_term);
        Ok(())
    }

    fn assert_not_term(&mut self, term: &SmtTerm) -> anyhow::Result<()> {
        let cvc5_term = self.convert_assertion_term(term)?;
        let not_term = self.tm.mk_term(Kind::Not, &[cvc5_term]);
        self.solver.assert_formula(not_term);
        Ok(())
    }

    fn assert_terms_conjunctively(&mut self, terms: &[SmtTerm]) -> anyhow::Result<()> {
        match terms {
            [] => Ok(()),
            [term] => self.assert_term(term),
            _ => {
                let children = terms
                    .iter()
                    .map(|term| self.convert_assertion_term(term))
                    .collect::<anyhow::Result<Vec<_>>>()?;
                let conjunction = self.tm.mk_term(Kind::And, &children);
                self.solver.assert_formula(conjunction);
                Ok(())
            }
        }
    }

    fn assert_tracked_term(&mut self, term: &SmtTerm, label: &str) -> anyhow::Result<()> {
        let label_term = self.tm.mk_const(self.tm.boolean_sort(), label);
        let cvc5_term = self.convert_assertion_term(term)?;
        let implication = self
            .tm
            .mk_term(Kind::Implies, &[label_term.clone(), cvc5_term]);
        self.solver.assert_formula(implication);
        self.tracked_labels.push((label.to_string(), label_term));
        Ok(())
    }

    fn push(&mut self) {
        self.solver.push(1);
    }

    fn pop(&mut self, levels: u32) {
        self.solver.pop(levels);
    }

    fn check(&mut self) -> SolverCheckResult {
        let assumptions = self
            .tracked_labels
            .iter()
            .map(|(_, term)| term.clone())
            .collect::<Vec<_>>();
        let result = if assumptions.is_empty() {
            self.solver.check_sat()
        } else {
            self.solver.check_sat_assuming(&assumptions)
        };
        let check_result = SolverCheckResult::from_cvc5(&result);
        self.last_result = Some(check_result);
        check_result
    }

    fn check_and_record_statistics(&mut self) -> SolverCheckResult {
        let start_time = Instant::now();
        let result = self.check();
        self.solver_statistics
            .add_time("solver_time", start_time.elapsed().as_secs_f64());
        result
    }

    fn record_statistics_since(&mut self, start_time: Instant) {
        self.solver_statistics
            .add_time("solver_time", start_time.elapsed().as_secs_f64());
    }

    fn has_model(&self) -> bool {
        self.last_result == Some(SolverCheckResult::Sat)
    }

    fn eval_to_string(&self, term: &SmtTerm) -> anyhow::Result<String> {
        if self.last_result != Some(SolverCheckResult::Sat) {
            anyhow::bail!("CVC5 model values are only available after SAT");
        }
        let cvc5_term = self.convert_term(term)?;
        Ok(self.solver.get_value(cvc5_term).to_string())
    }

    fn model_to_string(&self) -> anyhow::Result<String> {
        if self.last_result != Some(SolverCheckResult::Sat) {
            return Ok("<no model>".to_string());
        }
        Ok("<CVC5 model dump is not implemented in Phase 4>".to_string())
    }

    fn get_solver_statistics(&self) -> SolverStatistics {
        self.solver_statistics.clone()
    }

    fn statistics_ref(&self) -> &SolverStatistics {
        &self.solver_statistics
    }

    fn get_reason_unknown(&self) -> Option<String> {
        None
    }

    fn get_unsat_core(&self) -> anyhow::Result<Vec<String>> {
        let assumptions = self.solver.get_unsat_assumptions();
        let labels = assumptions
            .iter()
            .map(|assumption| {
                self.tracked_labels
                    .iter()
                    .find(|(_, label_term)| label_term == assumption)
                    .map(|(label, _)| label.clone())
                    .unwrap_or_else(|| assumption.to_string())
            })
            .collect();
        Ok(labels)
    }

    fn to_smt2_string(&self) -> anyhow::Result<String> {
        anyhow::bail!("CVC5 solver SMT2 dumping is not implemented in Phase 4")
    }
}

impl SolverCheckResult {
    fn from_cvc5(result: &cvc5::Result<'_>) -> Self {
        if result.is_sat() {
            SolverCheckResult::Sat
        } else if result.is_unsat() {
            SolverCheckResult::Unsat
        } else {
            SolverCheckResult::Unknown
        }
    }
}

fn indexed_identifier_parts(qual_identifier: &QualIdentifier) -> Option<(&str, &[Index])> {
    match qual_identifier {
        QualIdentifier::Simple {
            identifier: Identifier::Indexed { symbol, indices },
        }
        | QualIdentifier::Sorted {
            identifier: Identifier::Indexed { symbol, indices },
            ..
        } => Some((&symbol.0, indices)),
        _ => None,
    }
}

fn single_numeral_index(context: &str, indices: &[Index]) -> anyhow::Result<u32> {
    if indices.len() != 1 {
        anyhow::bail!("{context} expects exactly one numeric index");
    }
    numeral_index(context, &indices[0])
}

fn numeral_index(context: &str, index: &Index) -> anyhow::Result<u32> {
    match index {
        Index::Numeral(value) => value
            .to_string()
            .parse::<u32>()
            .map_err(|error| anyhow::anyhow!("{context} index is not a u32: {error}")),
        Index::Symbol(symbol) => anyhow::bail!("{context} index must be numeric: {symbol}"),
    }
}

fn identifier_name(identifier: &Identifier) -> String {
    match identifier {
        Identifier::Simple { symbol } => symbol.0.clone(),
        Identifier::Indexed { symbol, indices } => {
            format!(
                "{}{}",
                symbol.0,
                indices
                    .iter()
                    .map(|index| format!("_{index}"))
                    .collect::<String>()
            )
        }
    }
}

fn attribute_value_to_option_string(
    value: &AttributeValue<Constant, Symbol, smt2parser::concrete::SExpr>,
) -> Option<String> {
    match value {
        AttributeValue::Constant(Constant::String(value)) => Some(value.clone()),
        AttributeValue::Constant(Constant::Numeral(value)) => Some(value.to_string()),
        AttributeValue::Symbol(symbol) => Some(symbol.0.clone()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use smt2parser::concrete::{Command, Identifier, QualIdentifier, Sort, Symbol, Term};
    use smt2parser::visitors::Index;

    use super::*;

    fn int_sort() -> Sort {
        Sort::Simple {
            identifier: Identifier::Simple {
                symbol: Symbol("Int".to_string()),
            },
        }
    }

    fn bitvec_sort(width: u32) -> Sort {
        Sort::Simple {
            identifier: Identifier::Indexed {
                symbol: Symbol("BitVec".to_string()),
                indices: vec![Index::Numeral(width.into())],
            },
        }
    }

    fn array_sort(index: Sort, value: Sort) -> Sort {
        Sort::Parameterized {
            identifier: Identifier::Simple {
                symbol: Symbol("Array".to_string()),
            },
            parameters: vec![index, value],
        }
    }

    fn symbol_term(name: &str) -> Term {
        Term::QualIdentifier(QualIdentifier::simple(name))
    }

    fn app(name: &str, args: Vec<Term>) -> Term {
        Term::Application {
            qual_identifier: QualIdentifier::simple(name),
            arguments: args,
        }
    }

    fn parsed_term(term: &str) -> Term {
        term.parse::<Term>().unwrap()
    }

    #[test]
    fn cvc5_solves_simple_lia_sat() {
        let mut solver = Cvc5SolverBackend::new("QF_LIA");
        solver
            .accept_command(&Command::DeclareConst {
                symbol: Symbol("x".to_string()),
                sort: int_sort(),
            })
            .unwrap();
        solver
            .assert_term(&app(
                ">",
                vec![symbol_term("x"), "0".parse::<Term>().unwrap()],
            ))
            .unwrap();
        assert_eq!(solver.check(), SolverCheckResult::Sat);
        assert!(!solver.eval_to_string(&symbol_term("x")).unwrap().is_empty());
    }

    #[test]
    fn cvc5_solves_simple_lia_unsat() {
        let mut solver = Cvc5SolverBackend::new("QF_LIA");
        solver
            .accept_command(&Command::DeclareConst {
                symbol: Symbol("x".to_string()),
                sort: int_sort(),
            })
            .unwrap();
        solver
            .assert_term(&app(
                ">",
                vec![symbol_term("x"), "0".parse::<Term>().unwrap()],
            ))
            .unwrap();
        solver
            .assert_term(&app(
                "<=",
                vec![symbol_term("x"), "0".parse::<Term>().unwrap()],
            ))
            .unwrap();
        assert_eq!(solver.check(), SolverCheckResult::Unsat);
    }

    #[test]
    fn cvc5_solves_native_array_select_store() {
        let mut solver = Cvc5SolverBackend::new("ALL");
        for (name, sort) in [
            ("arr", array_sort(int_sort(), int_sort())),
            ("idx", int_sort()),
            ("val", int_sort()),
        ] {
            solver
                .accept_command(&Command::DeclareConst {
                    symbol: Symbol(name.to_string()),
                    sort,
                })
                .unwrap();
        }

        solver
            .assert_term(&parsed_term(
                "(not (= (select (store arr idx val) idx) val))",
            ))
            .unwrap();
        assert_eq!(solver.check(), SolverCheckResult::Unsat);
    }

    #[test]
    fn cvc5_solves_array_bitvector_select_store() {
        let mut solver = Cvc5SolverBackend::new("ALL");
        for (name, sort) in [
            ("arr", array_sort(bitvec_sort(5), bitvec_sort(32))),
            ("idx", bitvec_sort(5)),
            ("val", bitvec_sort(32)),
        ] {
            solver
                .accept_command(&Command::DeclareConst {
                    symbol: Symbol(name.to_string()),
                    sort,
                })
                .unwrap();
        }

        solver
            .assert_term(&parsed_term(
                "(not (= (select (store arr idx val) idx) val))",
            ))
            .unwrap();
        assert_eq!(solver.check(), SolverCheckResult::Unsat);
    }

    #[test]
    fn cvc5_solves_bitvector_literals_and_indexed_ops() {
        let mut solver = Cvc5SolverBackend::new("ALL");
        for term in [
            "(= ((_ extract 3 0) #x2a) (_ bv10 4))",
            "(= ((_ zero_extend 4) (_ bv15 4)) (_ bv15 8))",
            "(= ((_ sign_extend 4) (_ bv15 4)) (_ bv255 8))",
            "(= (concat (_ bv10 4) (_ bv5 4)) (_ bv165 8))",
            "(= (bvand (_ bv15 4) (_ bv10 4)) (_ bv10 4))",
            "(= (bvor (_ bv1 4) (_ bv2 4) (_ bv4 4)) (_ bv7 4))",
            "(= (bvadd (_ bv1 8) (_ bv2 8) (_ bv3 8)) (_ bv6 8))",
        ] {
            solver.assert_term(&parsed_term(term)).unwrap();
        }

        assert_eq!(solver.check(), SolverCheckResult::Sat);
    }

    #[test]
    fn cvc5_solves_constant_array() {
        let mut solver = Cvc5SolverBackend::new("ALL");
        solver
            .assert_term(&parsed_term(
                "(not (= (select ((as const (Array Int Int)) 7) 0) 7))",
            ))
            .unwrap();
        assert_eq!(solver.check(), SolverCheckResult::Unsat);
    }

    #[test]
    fn cvc5_solves_forall_assertion() {
        let mut solver = Cvc5SolverBackend::new("ALL");
        solver
            .assert_term(&parsed_term("(forall ((x Int)) (= x x))"))
            .unwrap();
        assert_eq!(solver.check(), SolverCheckResult::Sat);
    }

    #[test]
    fn cvc5_recovers_tracked_unsat_core_labels() {
        let mut solver: Box<dyn YardbirdSolver> = Box::new(Cvc5SolverBackend::new("QF_LIA"));
        solver
            .accept_command(&Command::DeclareConst {
                symbol: Symbol("x".to_string()),
                sort: int_sort(),
            })
            .unwrap();

        solver
            .assert_tracked_instantiation(
                "positive_inst",
                &app(">", vec![symbol_term("x"), parsed_term("0")]),
            )
            .unwrap();
        solver
            .assert_tracked_instantiation(
                "nonpositive_inst",
                &app("<=", vec![symbol_term("x"), parsed_term("0")]),
            )
            .unwrap();

        assert_eq!(solver.check(), SolverCheckResult::Unsat);
        let core = solver.get_unsat_core().unwrap();
        assert!(core.contains(&"positive_inst".to_string()));
        assert!(core.contains(&"nonpositive_inst".to_string()));
    }
}
