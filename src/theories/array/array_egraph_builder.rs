//! Staged construction of the model-equivalence e-graph used for array refinement.

use std::{collections::HashSet, fmt::Debug};

use smt2parser::{concrete::Term, vmt::split_framed_symbol};

use crate::{
    problem_context::ProblemContext,
    theories::array::{
        array_axioms::{translate_term, ArrayLanguage},
        array_conflict_scheduler::preprocess_array_expr,
        property_cone::PropertyCone,
    },
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArrayEGraphBuildStage {
    Cone,
    Full,
}

impl ArrayEGraphBuildStage {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Cone => "cone",
            Self::Full => "full",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ArrayEGraphExpansion {
    pub stage: ArrayEGraphBuildStage,
    pub total_subterms: usize,
    pub admitted_subterms: usize,
    pub newly_admitted_subterms: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArrayEGraphBuildStep {
    Expanded(ArrayEGraphExpansion),
    Exhausted,
}

/// Controls which model equalities are admitted before array-axiom matching.
///
/// Repeated calls expand the same e-graph. `Exhausted` means that the adapter
/// has no broader construction stage and exhaustive matching may safely hand
/// control to concrete validation.
pub trait ArrayEGraphBuilder: Debug + Send {
    fn clone_box(&self) -> Box<dyn ArrayEGraphBuilder>;

    fn requires_property_cone(&self) -> bool {
        false
    }

    fn expand(
        &mut self,
        egraph: &mut egg::EGraph<ArrayLanguage, ()>,
        smt: &dyn ProblemContext,
        property_cone: &PropertyCone,
    ) -> anyhow::Result<ArrayEGraphBuildStep>;
}

impl Clone for Box<dyn ArrayEGraphBuilder> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

#[derive(Clone, Debug, Default)]
pub struct FullEGraphBuilder {
    admitted: HashSet<Term>,
    expanded: bool,
}

impl ArrayEGraphBuilder for FullEGraphBuilder {
    fn clone_box(&self) -> Box<dyn ArrayEGraphBuilder> {
        Box::new(self.clone())
    }

    fn expand(
        &mut self,
        egraph: &mut egg::EGraph<ArrayLanguage, ()>,
        smt: &dyn ProblemContext,
        _property_cone: &PropertyCone,
    ) -> anyhow::Result<ArrayEGraphBuildStep> {
        if self.expanded {
            return Ok(ArrayEGraphBuildStep::Exhausted);
        }
        self.expanded = true;
        let subterms = smt.get_all_subterms();
        let total_subterms = subterms.len();
        let newly_admitted_subterms = add_subterms(egraph, smt, &subterms, &mut self.admitted)?;
        Ok(ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
            stage: ArrayEGraphBuildStage::Full,
            total_subterms,
            admitted_subterms: self.admitted.len(),
            newly_admitted_subterms,
        }))
    }
}

#[derive(Clone, Copy, Debug, Default)]
enum ConeThenFullStage {
    #[default]
    Cone,
    Full,
    Exhausted,
}

#[derive(Clone, Debug, Default)]
pub struct ConeThenFullEGraphBuilder {
    admitted: HashSet<Term>,
    stage: ConeThenFullStage,
}

impl ArrayEGraphBuilder for ConeThenFullEGraphBuilder {
    fn clone_box(&self) -> Box<dyn ArrayEGraphBuilder> {
        Box::new(self.clone())
    }

    fn requires_property_cone(&self) -> bool {
        true
    }

    fn expand(
        &mut self,
        egraph: &mut egg::EGraph<ArrayLanguage, ()>,
        smt: &dyn ProblemContext,
        property_cone: &PropertyCone,
    ) -> anyhow::Result<ArrayEGraphBuildStep> {
        match self.stage {
            ConeThenFullStage::Cone => {
                let subterms = smt.get_all_subterms();
                let total_subterms = subterms.len();
                let cone_symbols = property_cone
                    .array_distances
                    .keys()
                    .cloned()
                    .collect::<HashSet<_>>();
                let cone_terms = cone_admitted_subterms(&subterms, &cone_symbols);
                let cone_refs = subterms
                    .iter()
                    .copied()
                    .filter(|term| cone_terms.contains(*term))
                    .collect::<Vec<_>>();

                if cone_refs.is_empty() || cone_refs.len() == total_subterms {
                    self.stage = ConeThenFullStage::Exhausted;
                    let newly_admitted_subterms =
                        add_subterms(egraph, smt, &subterms, &mut self.admitted)?;
                    return Ok(ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
                        stage: ArrayEGraphBuildStage::Full,
                        total_subterms,
                        admitted_subterms: self.admitted.len(),
                        newly_admitted_subterms,
                    }));
                }

                self.stage = ConeThenFullStage::Full;
                let newly_admitted_subterms =
                    add_subterms(egraph, smt, &cone_refs, &mut self.admitted)?;
                Ok(ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
                    stage: ArrayEGraphBuildStage::Cone,
                    total_subterms,
                    admitted_subterms: self.admitted.len(),
                    newly_admitted_subterms,
                }))
            }
            ConeThenFullStage::Full => {
                self.stage = ConeThenFullStage::Exhausted;
                let subterms = smt.get_all_subterms();
                let total_subterms = subterms.len();
                let newly_admitted_subterms =
                    add_subterms(egraph, smt, &subterms, &mut self.admitted)?;
                Ok(ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
                    stage: ArrayEGraphBuildStage::Full,
                    total_subterms,
                    admitted_subterms: self.admitted.len(),
                    newly_admitted_subterms,
                }))
            }
            ConeThenFullStage::Exhausted => Ok(ArrayEGraphBuildStep::Exhausted),
        }
    }
}

fn add_subterms(
    egraph: &mut egg::EGraph<ArrayLanguage, ()>,
    smt: &dyn ProblemContext,
    subterms: &[&Term],
    admitted: &mut HashSet<Term>,
) -> anyhow::Result<usize> {
    let mut newly_admitted = 0;
    for term in subterms {
        if !admitted.insert((*term).clone()) {
            continue;
        }
        newly_admitted += 1;
        let interp_str = smt.eval_to_string(term)?;
        let translated = translate_term((*term).clone())
            .ok_or_else(|| anyhow::anyhow!("could not translate array refinement term: {term}"))?;
        let preprocessed = preprocess_array_expr(&interp_str);
        let parsed_interp = preprocessed.parse()?;
        let term_id = egraph.add_expr(&translated);
        let interp_id = egraph.add_expr(&parsed_interp);
        egraph.union(term_id, interp_id);
    }
    egraph.rebuild();
    Ok(newly_admitted)
}

fn cone_admitted_subterms(subterms: &[&Term], cone_symbols: &HashSet<String>) -> HashSet<Term> {
    let cone_symbols = cone_symbols
        .iter()
        .filter_map(|symbol| canonical_leaf_symbol(symbol))
        .collect::<HashSet<_>>();
    let mut admitted = HashSet::new();
    for term in subterms {
        if term_contains_cone_symbol(term, &cone_symbols) {
            collect_term_dependencies(term, &mut admitted);
        }
    }
    admitted
}

fn term_contains_cone_symbol(term: &Term, cone_symbols: &HashSet<String>) -> bool {
    match term {
        Term::QualIdentifier(identifier) => canonical_leaf_symbol(&identifier.get_name())
            .is_some_and(|symbol| cone_symbols.contains(&symbol)),
        Term::Application { arguments, .. } => arguments
            .iter()
            .any(|argument| term_contains_cone_symbol(argument, cone_symbols)),
        Term::Let { var_bindings, term } => {
            var_bindings
                .iter()
                .any(|(_, value)| term_contains_cone_symbol(value, cone_symbols))
                || term_contains_cone_symbol(term, cone_symbols)
        }
        Term::Forall { term, .. } | Term::Exists { term, .. } | Term::Attributes { term, .. } => {
            term_contains_cone_symbol(term, cone_symbols)
        }
        Term::Match { term, cases } => {
            term_contains_cone_symbol(term, cone_symbols)
                || cases
                    .iter()
                    .any(|(_, case)| term_contains_cone_symbol(case, cone_symbols))
        }
        Term::Constant(_) => false,
    }
}

fn collect_term_dependencies(term: &Term, admitted: &mut HashSet<Term>) {
    if !admitted.insert(term.clone()) {
        return;
    }
    match term {
        Term::Application { arguments, .. } => {
            for argument in arguments {
                collect_term_dependencies(argument, admitted);
            }
        }
        Term::Let { var_bindings, term } => {
            for (_, value) in var_bindings {
                collect_term_dependencies(value, admitted);
            }
            collect_term_dependencies(term, admitted);
        }
        Term::Forall { term, .. } | Term::Exists { term, .. } | Term::Attributes { term, .. } => {
            collect_term_dependencies(term, admitted)
        }
        Term::Match { term, cases } => {
            collect_term_dependencies(term, admitted);
            for (_, case) in cases {
                collect_term_dependencies(case, admitted);
            }
        }
        Term::Constant(_) | Term::QualIdentifier(_) => {}
    }
}

fn canonical_leaf_symbol(symbol: &str) -> Option<String> {
    let symbol = symbol.strip_prefix('|').unwrap_or(symbol);
    let symbol = symbol.strip_suffix('|').unwrap_or(symbol);
    if symbol.is_empty()
        || symbol.contains(char::is_whitespace)
        || symbol.starts_with('(')
        || symbol.ends_with(')')
    {
        return None;
    }
    Some(
        split_framed_symbol(symbol)
            .map(|(base, _)| base)
            .unwrap_or_else(|| symbol.to_string()),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use smt2parser::vmt::{quantified_instantiator::Instance, variable::Variable, ReadsAndWrites};

    use crate::utils::SolverStatistics;

    struct FakeContext {
        terms: Vec<Term>,
    }

    impl ProblemContext for FakeContext {
        fn as_any(&self) -> &dyn std::any::Any {
            self
        }

        fn has_model(&self) -> bool {
            true
        }

        fn eval_to_string(&self, term: &Term) -> anyhow::Result<String> {
            Ok(term.to_string())
        }

        fn model_to_string(&self) -> anyhow::Result<String> {
            Ok(String::new())
        }

        fn get_all_subterms(&self) -> Vec<&Term> {
            self.terms.iter().collect()
        }

        fn get_solver_statistics(&self) -> SolverStatistics {
            SolverStatistics::default()
        }

        fn get_reason_unknown(&self) -> Option<String> {
            None
        }

        fn add_instantiation(
            &mut self,
            _inst: Instance,
            _abstract_instantiation_id: Option<String>,
        ) -> bool {
            false
        }

        fn get_instantiations(&self) -> Vec<Term> {
            vec![]
        }

        fn get_variables(&self) -> &[Variable] {
            &[]
        }

        fn get_number_instantiations_added(&self) -> u64 {
            0
        }

        fn get_init_and_transition_subterms(&self) -> Vec<String> {
            vec![]
        }

        fn get_property_subterms(&self) -> Vec<String> {
            vec![]
        }

        fn get_reads_and_writes(&self) -> ReadsAndWrites {
            ReadsAndWrites::default()
        }

        fn get_array_types(&self) -> Vec<(String, String)> {
            vec![("Int".to_string(), "Int".to_string())]
        }
    }

    #[test]
    fn cone_admission_keeps_dependencies_and_excludes_unrelated_terms() {
        let relevant: Term = "(Read_Int_Int a@3 (+ i@3 1))".parse().unwrap();
        let unrelated: Term = "(Read_Int_Int b@3 j@3)".parse().unwrap();
        let subterms = vec![&relevant, &unrelated];
        let admitted = cone_admitted_subterms(&subterms, &HashSet::from(["a".to_string()]));

        assert!(admitted.contains(&relevant));
        assert!(!admitted.contains(&unrelated));
        assert!(admitted.iter().any(|term| term.to_string() == "a@3"));
        assert!(admitted.iter().any(|term| term.to_string() == "i@3"));
    }

    #[test]
    fn cone_then_full_expands_the_same_egraph_before_exhaustion() {
        let context = FakeContext {
            terms: vec![
                "(Read_Int_Int a@3 i@3)".parse().unwrap(),
                "(Read_Int_Int b@3 j@3)".parse().unwrap(),
            ],
        };
        let cone = PropertyCone {
            array_distances: [("a".to_string(), 0)].into_iter().collect(),
            ..PropertyCone::default()
        };
        let mut builder = ConeThenFullEGraphBuilder::default();
        let mut egraph = egg::EGraph::new(());

        let first = builder.expand(&mut egraph, &context, &cone).unwrap();
        let classes_after_cone = egraph.number_of_classes();
        let second = builder.expand(&mut egraph, &context, &cone).unwrap();
        let classes_after_full = egraph.number_of_classes();
        let third = builder.expand(&mut egraph, &context, &cone).unwrap();

        assert!(matches!(
            first,
            ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
                stage: ArrayEGraphBuildStage::Cone,
                ..
            })
        ));
        assert!(matches!(
            second,
            ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
                stage: ArrayEGraphBuildStage::Full,
                ..
            })
        ));
        assert_eq!(third, ArrayEGraphBuildStep::Exhausted);
        assert!(classes_after_full > classes_after_cone);
    }
}
