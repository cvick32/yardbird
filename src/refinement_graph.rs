//! One model-equivalence graph. Construction admits vocabulary between searches;
//! matching only receives an immutable e-graph borrow.
mod vocabulary;

use std::collections::{HashMap, HashSet};

use egg::Language;
use smt2parser::concrete::{Command, Sort, Term};

use crate::problem_context::ProblemContext;
use crate::terms::language::{translate_term_with_array_types, TermExpr, TermLanguage};

#[derive(Default)]
pub struct RefinementGraph {
    pub(crate) egraph: egg::EGraph<TermLanguage, ()>,
    signatures: HashMap<String, (Vec<Sort>, Sort)>,
    context_registered: bool,
    growth: Option<vocabulary::VocabularyGrowth>,
    values: HashMap<(Sort, String), egg::Id>,
    domain_sorts: HashSet<Sort>,
    pub(crate) terms: Vec<TermExpr>,
    originals: Vec<(egg::Id, TermExpr)>,
    seen_terms: HashSet<TermExpr>,
    seen_originals: HashSet<egg::Id>,
    pub(crate) evaluations: HashMap<Term, String>,
}

impl std::ops::Deref for RefinementGraph {
    type Target = egg::EGraph<TermLanguage, ()>;
    fn deref(&self) -> &Self::Target {
        &self.egraph
    }
}

impl RefinementGraph {
    pub(crate) fn new(signatures: HashMap<String, (Vec<Sort>, Sort)>) -> Self {
        Self {
            signatures,
            ..Self::default()
        }
    }

    fn register_context(&mut self, smt: &dyn ProblemContext) {
        if self.context_registered {
            return;
        }
        self.context_registered = true;
        for declaration in smt.get_refinement_declarations() {
            let (symbol, parameters, sort) = match declaration {
                Command::DeclareFun {
                    symbol,
                    parameters,
                    sort,
                } => (symbol, parameters, sort),
                Command::DeclareConst { symbol, sort } => (symbol, vec![], sort),
                Command::DefineFun { sig, .. } => (
                    sig.name,
                    sig.parameters.into_iter().map(|(_, s)| s).collect(),
                    sig.result,
                ),
                _ => continue,
            };
            // Declarations already have the representation chosen by preparation.
            self.signatures
                .entry(symbol.0)
                .or_insert((parameters, sort));
        }
        for (index, value) in smt.get_array_types() {
            let parse = smt2parser::vmt::array_abstractor::string_to_sort;
            let array = parse(&format!("Array_{index}_{value}"));
            let is = parse(&index);
            let vs = parse(&value);
            for (name, arguments, result) in [
                (
                    format!("Read_{index}_{value}"),
                    vec![array.clone(), is.clone()],
                    vs.clone(),
                ),
                (
                    format!("Write_{index}_{value}"),
                    vec![array.clone(), is.clone(), vs.clone()],
                    array.clone(),
                ),
                (format!("ConstArr_{index}_{value}"), vec![vs], array),
            ] {
                self.signatures.entry(name).or_insert((arguments, result));
            }
        }
    }

    pub(crate) fn set_domain_sorts(&mut self, sorts: HashSet<Sort>) {
        self.domain_sorts = sorts;
    }

    /// Admit a problem term and its typed model equivalence. Domain membership
    /// and original representatives are metadata, never solver assertions.
    pub fn admit(
        &mut self,
        smt: &dyn ProblemContext,
        term: &Term,
        model_literals: bool,
    ) -> anyhow::Result<()> {
        self.register_context(smt);
        let expression = translate_term_with_array_types(term.clone(), &smt.get_array_types())
            .ok_or_else(|| anyhow::anyhow!("could not translate refinement term: {term}"))?;
        let id = self.egraph.add_expr(&expression);
        let mut ids = Vec::new();
        for node in expression.as_ref() {
            let id = self
                .egraph
                .add(node.clone().map_children(|child| ids[usize::from(child)]));
            ids.push(id);
            if self.seen_originals.insert(id) {
                self.originals
                    .push((id, node.build_recexpr(|child| expression[child].clone())));
            }
        }
        if self.seen_terms.insert(expression.clone()) {
            self.terms.push(expression);
        }
        let sort_term = match term {
            Term::Application {
                qual_identifier,
                arguments,
            } if arguments.is_empty() => Term::QualIdentifier(qual_identifier.clone()),
            _ => term.clone(),
        };
        let sort =
            crate::theories::quantifiers::term_sort(&sort_term, &self.signatures, &HashMap::new())
                .ok();
        // Binder admission evaluates only its typed domains. Array admission
        // additionally needs model values for built-in axiom matching.
        if !model_literals && !sort.as_ref().is_some_and(|s| self.domain_sorts.contains(s)) {
            return Ok(());
        }
        let value = match self.evaluations.get(term) {
            Some(value) => value.clone(),
            None => {
                let value = smt.eval_to_string(term)?;
                self.evaluations.insert(term.clone(), value.clone());
                value
            }
        };
        if let Some(sort) = &sort {
            if let Some(other) = self.values.insert((sort.clone(), value.clone()), id) {
                self.egraph.union(id, other);
            }
            if self.domain_sorts.contains(sort) {
                let sort_id = self
                    .egraph
                    .add(TermLanguage::SortTag(sort.to_string().into()));
                self.egraph.add(TermLanguage::Domain([sort_id, id]));
            }
        }
        if model_literals && !value.contains("!val!") {
            // Literal values are useful array representatives, but an SMT
            // model's private elements must never become candidate terms.
            let value_sort = value.parse::<Term>().ok().and_then(|t| {
                crate::theories::quantifiers::term_sort(&t, &self.signatures, &HashMap::new()).ok()
            });
            if sort.is_some() && sort == value_sort {
                let raw = crate::terms::preprocess::preprocess_array_expr(&value);
                let parsed: TermExpr = raw.parse()?;
                let value_id = self.egraph.add_expr(&parsed);
                self.egraph.union(id, value_id);
            }
        }
        Ok(())
    }

    pub fn rebuild(&mut self) {
        self.egraph.rebuild();
    }

    pub(crate) fn representatives(&self) -> HashMap<egg::Id, TermExpr> {
        let mut result = HashMap::new();
        for (id, expression) in &self.originals {
            result
                .entry(self.egraph.find(*id))
                .or_insert_with(|| expression.clone());
        }
        result
    }
}
