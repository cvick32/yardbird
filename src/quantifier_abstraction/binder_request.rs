//! A directed request keeps symbolic arguments separate from model-local IDs.
//! Scheduling decides which request to make; this module only constrains and
//! resumes matching. It does not infer or assert prerequisites.

use super::*;
use crate::theories::array::{array_axioms::ArrayExpr, quantified_search::BinderSearchCursor};
use std::rc::Rc;

/// Names refer to the lowered helper and its capture/bound-variable symbols.
/// Missing bindings are found by egg. An empty list selects just this rule.
/// The ordinary instance direction is used for Expand; Witnesses explicitly
/// selects the opposite direction and accepts only capture bindings.
/// Partial requests search the prepared graph's existing vocabulary; fully
/// bound requests may introduce new helper applications. Repeating a request
/// resumes its cursor; a new solver model creates fresh request state.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct BinderSearchRequest {
    pub helper: String,
    pub phase: SearchPhase,
    pub bindings: Vec<(Symbol, Term)>,
}

pub(crate) enum BinderSearch<'a> {
    Phase(SearchPhase),
    Request(&'a BinderSearchRequest),
}

impl From<SearchPhase> for BinderSearch<'_> {
    fn from(phase: SearchPhase) -> Self {
        Self::Phase(phase)
    }
}

impl<'a> From<&'a BinderSearchRequest> for BinderSearch<'a> {
    fn from(request: &'a BinderSearchRequest) -> Self {
        Self::Request(request)
    }
}

pub(super) struct PreparedBinderRequest {
    rule: Rc<CompiledQuantifiedRule<()>>,
    pub cursor: BinderSearchCursor,
}

impl PreparedQuantifierSearch {
    pub(super) fn prepare_request(
        &mut self,
        request: &BinderSearchRequest,
    ) -> anyhow::Result<Rc<CompiledQuantifiedRule<()>>> {
        if let Some(prepared) = self.requests.get(request) {
            return Ok(prepared.rule.clone());
        }
        let rule = self
            .compiled
            .sources
            .iter()
            .find(|rule| rule.name == request.helper)
            .ok_or_else(|| anyhow::anyhow!("unknown binder helper {}", request.helper))?;
        let mut seen = HashSet::new();
        for (symbol, term) in &request.bindings {
            anyhow::ensure!(seen.insert(symbol), "duplicate binding for {symbol}");
            anyhow::ensure!(
                !contains_binders(term),
                "binding {symbol} must be quantifier-free"
            );
            let (_, expected) = rule
                .captures
                .iter()
                .chain(&rule.variables)
                .find(|(name, _)| name == symbol)
                .ok_or_else(|| anyhow::anyhow!("unknown binding {symbol} for {}", rule.name))?;
            anyhow::ensure!(
                request.phase != SearchPhase::Witnesses
                    || rule.captures.iter().any(|(name, _)| name == symbol),
                "witness requests bind captures, not quantified variable {symbol}"
            );
            anyhow::ensure!(
                !rule.unit_capture
                    || !rule.captures.iter().any(|(name, _)| name == symbol)
                    || term == &app("true", vec![]),
                "the dummy capture must be true"
            );
            let actual = term_sort(term, &self.compiled.signatures, &HashMap::new())?;
            anyhow::ensure!(
                abstract_sort(&actual) == abstract_sort(expected),
                "binding {symbol} expects {expected}, got {actual}"
            );
        }
        let compiled = rule
            .compile_with_bindings(request.phase, &self.compiled.types, &request.bindings)
            .ok_or_else(|| anyhow::anyhow!("binder {} has no witness direction", rule.name))??;
        let rule = Rc::new(compiled);
        self.requests.insert(
            request.clone(),
            PreparedBinderRequest {
                rule: rule.clone(),
                cursor: BinderSearchCursor::default(),
            },
        );
        Ok(rule)
    }
}

/// Substitute at the pattern level so a supplied symbol can never accidentally
/// become a pattern variable. Literals also survive cost-based extraction.
pub(super) fn specialize(
    pattern: egg::Pattern<ArrayLanguage>,
    bindings: &[(egg::Var, ArrayExpr)],
) -> egg::Pattern<ArrayLanguage> {
    use egg::{ENodeOrVar, Language};
    if bindings.is_empty() {
        return pattern;
    }
    let mut result = egg::PatternAst::default();
    let mut ids = Vec::new();
    for node in pattern.ast.as_ref() {
        let id = match node {
            ENodeOrVar::Var(var) if bindings.iter().any(|(bound, _)| bound == var) => {
                let expression = &bindings.iter().find(|(bound, _)| bound == var).unwrap().1;
                let mut children = Vec::new();
                for node in expression.as_ref() {
                    children.push(result.add(ENodeOrVar::ENode(
                        node.clone().map_children(|id| children[usize::from(id)]),
                    )));
                }
                *children.last().expect("binding expressions are nonempty")
            }
            node => result.add(node.clone().map_children(|id| ids[usize::from(id)])),
        };
        ids.push(id);
    }
    egg::Pattern::new(result)
}
