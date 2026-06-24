use std::{collections::HashMap, time::Instant};

use cvc5::{Kind, Solver, Sort, Term, TermManager};
use smt2parser::concrete::{
    AttributeValue, Command, Constant, Identifier, QualIdentifier, Sort as SmtSort, Symbol,
    Term as SmtTerm,
};

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
        solver.set_option("incremental", "true");
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
            SmtSort::Simple { identifier } => match identifier_name(identifier).as_str() {
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
            SmtSort::Parameterized { identifier, .. } => {
                anyhow::bail!(
                    "CVC5 backend does not support parameterized sort {} until Phase 5",
                    identifier_name(identifier)
                )
            }
        }
    }

    fn convert_term(&self, term: &SmtTerm) -> anyhow::Result<Term<'static>> {
        match term {
            SmtTerm::Constant(Constant::Numeral(value)) => {
                Ok(self.tm.mk_integer_from_str(&value.to_string()))
            }
            SmtTerm::Constant(Constant::Decimal(value)) => {
                Ok(self.tm.mk_real_from_str(&value.to_string()))
            }
            SmtTerm::QualIdentifier(qual_identifier) => {
                self.convert_qual_identifier(qual_identifier)
            }
            SmtTerm::Application {
                qual_identifier,
                arguments,
            } => self.convert_application(qual_identifier, arguments),
            SmtTerm::Let { .. }
            | SmtTerm::Forall { .. }
            | SmtTerm::Exists { .. }
            | SmtTerm::Match { .. }
            | SmtTerm::Attributes { .. }
            | SmtTerm::Constant(Constant::Hexadecimal(_))
            | SmtTerm::Constant(Constant::Binary(_))
            | SmtTerm::Constant(Constant::String(_)) => {
                anyhow::bail!("CVC5 backend does not support term in Phase 4: {term}")
            }
        }
    }

    fn convert_qual_identifier(
        &self,
        qual_identifier: &QualIdentifier,
    ) -> anyhow::Result<Term<'static>> {
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

    fn convert_application(
        &self,
        qual_identifier: &QualIdentifier,
        arguments: &[SmtTerm],
    ) -> anyhow::Result<Term<'static>> {
        let name = qual_identifier.get_name();
        let args = arguments
            .iter()
            .map(|term| self.convert_term(term))
            .collect::<anyhow::Result<Vec<_>>>()?;

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
            ">" if args.len() == 2 => Ok(self.tm.mk_term(Kind::Gt, &args)),
            ">=" if args.len() == 2 => Ok(self.tm.mk_term(Kind::Geq, &args)),
            "<" if args.len() == 2 => Ok(self.tm.mk_term(Kind::Lt, &args)),
            "<=" if args.len() == 2 => Ok(self.tm.mk_term(Kind::Leq, &args)),
            _ => {
                if let Some(function) = self.terms.get(&name) {
                    let children = std::iter::once(function.clone())
                        .chain(args)
                        .collect::<Vec<_>>();
                    Ok(self.tm.mk_term(Kind::ApplyUf, &children))
                } else {
                    anyhow::bail!("unsupported CVC5 application in Phase 4: {name}")
                }
            }
        }
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
                    anyhow::bail!(
                        "CVC5 backend only supports zero-arity declare-sort in Phase 4: {symbol}"
                    );
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
                let value = self.convert_term(term)?;
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
                    "CVC5 backend only supports zero-argument define-fun in Phase 4: {}",
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
        let cvc5_term = self.convert_term(term)?;
        self.solver.assert_formula(cvc5_term);
        Ok(())
    }

    fn assert_not_term(&mut self, term: &SmtTerm) -> anyhow::Result<()> {
        let cvc5_term = self.convert_term(term)?;
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
                    .map(|term| self.convert_term(term))
                    .collect::<anyhow::Result<Vec<_>>>()?;
                let conjunction = self.tm.mk_term(Kind::And, &children);
                self.solver.assert_formula(conjunction);
                Ok(())
            }
        }
    }

    fn assert_tracked_term(&mut self, term: &SmtTerm, label: &str) -> anyhow::Result<()> {
        let label_term = self.tm.mk_const(self.tm.boolean_sort(), label);
        let cvc5_term = self.convert_term(term)?;
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
        Ok(self
            .solver
            .get_unsat_assumptions()
            .iter()
            .map(ToString::to_string)
            .collect())
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

    use super::*;

    fn int_sort() -> Sort {
        Sort::Simple {
            identifier: Identifier::Simple {
                symbol: Symbol("Int".to_string()),
            },
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
}
