//! Construction policies for the model-equivalence e-graph used for array refinement.

use std::{collections::HashSet, fmt::Debug};

use egg::Language;
use smt2parser::{concrete::Term, vmt::split_framed_symbol};

use crate::{
    problem_context::{ArrayCandidateCatalog, ProblemContext},
    theories::array::{
        array_axioms::{expr_to_term, translate_term, ArrayExpr, ArrayLanguage},
        array_dataflow::PropertyCone,
        array_expr_parser::preprocess_array_expr,
        candidate_scope::CandidateScope,
    },
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArrayEGraphBuildStage {
    Source,
    Cone,
    Full,
}

impl ArrayEGraphBuildStage {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Source => "source",
            Self::Cone => "cone",
            Self::Full => "full",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ArrayEGraphExpansion {
    pub stage: ArrayEGraphBuildStage,
    pub candidate_scope: CandidateScope,
    pub total_subterms: usize,
    pub admitted_subterms: usize,
    pub newly_admitted_subterms: usize,
    pub demand_frontier_sites: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ArrayEGraphBuildStep {
    Expanded(ArrayEGraphExpansion),
    Exhausted,
}

/// Controls which model equalities are admitted before array-axiom matching.
///
/// Repeated calls expand the same e-graph. `Exhausted` means that no broader construction
/// stage remains, so the abstract strategy must report abstraction exhaustion.
pub trait ArrayEGraphBuilder: Debug + Send {
    fn clone_box(&self) -> Box<dyn ArrayEGraphBuilder>;

    /// Create the builder for one refinement attempt at `depth`. Staged
    /// builders use the shared attempt set to widen when strategy setup creates
    /// a fresh state for another solver check at the same depth.
    fn clone_for_refinement(
        &self,
        attempted_depths: &mut HashSet<u16>,
        depth: u16,
    ) -> Box<dyn ArrayEGraphBuilder> {
        if self.requires_property_cone() && !attempted_depths.insert(depth) {
            Box::<FullEGraphBuilder>::default()
        } else {
            self.clone_box()
        }
    }

    fn requires_property_cone(&self) -> bool {
        false
    }

    /// Whether a source-stage batch is sparse enough that the next refinement
    /// at this depth should widen to all model terms.
    fn should_widen_after_source(&self, _selected_count: usize) -> bool {
        false
    }

    fn expand(
        &mut self,
        egraph: &mut egg::EGraph<ArrayLanguage, ()>,
        smt: &dyn ProblemContext,
        property_cone: &PropertyCone,
        depth: u16,
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
        _depth: u16,
    ) -> anyhow::Result<ArrayEGraphBuildStep> {
        if self.expanded {
            return Ok(ArrayEGraphBuildStep::Exhausted);
        }
        self.expanded = true;
        let subterms = smt.get_all_subterms();
        let total_subterms = subterms.len();
        let newly_admitted_subterms = add_subterms(egraph, smt, &subterms, &mut self.admitted)?;
        egraph.rebuild();
        Ok(ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
            stage: ArrayEGraphBuildStage::Full,
            candidate_scope: CandidateScope::AllCandidates,
            total_subterms,
            admitted_subterms: self.admitted.len(),
            newly_admitted_subterms,
            demand_frontier_sites: 0,
        }))
    }
}

#[derive(Clone, Copy, Debug, Default)]
enum SourceThenFullStage {
    #[default]
    Source,
    Full,
    Exhausted,
}

#[derive(Clone, Debug, Default)]
pub struct SourceThenFullEGraphBuilder {
    admitted: HashSet<Term>,
    stage: SourceThenFullStage,
}

impl ArrayEGraphBuilder for SourceThenFullEGraphBuilder {
    fn clone_box(&self) -> Box<dyn ArrayEGraphBuilder> {
        Box::new(self.clone())
    }

    fn clone_for_refinement(
        &self,
        attempted_depths: &mut HashSet<u16>,
        depth: u16,
    ) -> Box<dyn ArrayEGraphBuilder> {
        if attempted_depths.contains(&depth) {
            Box::<FullEGraphBuilder>::default()
        } else {
            self.clone_box()
        }
    }

    fn should_widen_after_source(&self, selected_count: usize) -> bool {
        selected_count <= 1
    }

    fn expand(
        &mut self,
        egraph: &mut egg::EGraph<ArrayLanguage, ()>,
        smt: &dyn ProblemContext,
        _property_cone: &PropertyCone,
        _depth: u16,
    ) -> anyhow::Result<ArrayEGraphBuildStep> {
        match self.stage {
            SourceThenFullStage::Source => {
                let subterms = smt.get_all_subterms();
                let source_subterms = smt.get_source_subterms();
                let total_subterms = subterms.len();
                if source_subterms.is_empty()
                    || (!smt.separates_source_subterms() && source_subterms.len() == total_subterms)
                {
                    self.stage = SourceThenFullStage::Exhausted;
                    let newly_admitted_subterms =
                        add_subterms(egraph, smt, &subterms, &mut self.admitted)?;
                    egraph.rebuild();
                    return Ok(ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
                        stage: ArrayEGraphBuildStage::Full,
                        candidate_scope: CandidateScope::AllCandidates,
                        total_subterms,
                        admitted_subterms: self.admitted.len(),
                        newly_admitted_subterms,
                        demand_frontier_sites: 0,
                    }));
                }

                self.stage = SourceThenFullStage::Full;
                let mut newly_admitted_subterms =
                    add_subterms(egraph, smt, &source_subterms, &mut self.admitted)?;
                let source_triggers = source_array_axiom_triggers(
                    &smt.get_array_candidate_catalog(),
                    &smt.get_property_subterms(),
                );
                let source_trigger_refs = source_triggers.iter().collect::<Vec<_>>();
                newly_admitted_subterms +=
                    add_subterms(egraph, smt, &source_trigger_refs, &mut self.admitted)?;
                egraph.rebuild();
                Ok(ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
                    stage: ArrayEGraphBuildStage::Source,
                    candidate_scope: CandidateScope::SourceGroundedOnly,
                    total_subterms,
                    admitted_subterms: self.admitted.len(),
                    newly_admitted_subterms,
                    demand_frontier_sites: 0,
                }))
            }
            SourceThenFullStage::Full => {
                self.stage = SourceThenFullStage::Exhausted;
                let subterms = smt.get_all_subterms();
                let total_subterms = subterms.len();
                let newly_admitted_subterms =
                    add_subterms(egraph, smt, &subterms, &mut self.admitted)?;
                egraph.rebuild();
                Ok(ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
                    stage: ArrayEGraphBuildStage::Full,
                    candidate_scope: CandidateScope::AllCandidates,
                    total_subterms,
                    admitted_subterms: self.admitted.len(),
                    newly_admitted_subterms,
                    demand_frontier_sites: 0,
                }))
            }
            SourceThenFullStage::Exhausted => Ok(ArrayEGraphBuildStep::Exhausted),
        }
    }
}

fn source_array_axiom_triggers(
    catalog: &ArrayCandidateCatalog,
    property_terms: &[String],
) -> Vec<Term> {
    let property_indices = property_terms
        .iter()
        .filter_map(|raw_term| raw_term.parse().ok().and_then(translate_term))
        .filter_map(|expression| {
            let Some(ArrayLanguage::ReadTyped([index_sort, value_sort, _, index])) =
                expression.as_ref().last()
            else {
                return None;
            };
            let (ArrayLanguage::Symbol(index_sort), ArrayLanguage::Symbol(value_sort)) =
                (&expression[*index_sort], &expression[*value_sort])
            else {
                return None;
            };
            Some((
                index_sort.as_str().to_string(),
                value_sort.as_str().to_string(),
                expression_at(&expression, *index),
            ))
        })
        .collect::<HashSet<_>>();
    let mut triggers = HashSet::new();
    for raw_term in &catalog.source_grounded.terms {
        let Some(expression) = raw_term.parse().ok().and_then(translate_term) else {
            continue;
        };
        let Some(ArrayLanguage::WriteTyped([index_sort, value_sort, _, index, _])) =
            expression.as_ref().last()
        else {
            continue;
        };
        let (ArrayLanguage::Symbol(index_sort), ArrayLanguage::Symbol(value_sort)) =
            (&expression[*index_sort], &expression[*value_sort])
        else {
            continue;
        };
        let index_sort = index_sort.as_str();
        let value_sort = value_sort.as_str();
        let write_index = expression_at(&expression, *index);
        let mut indices = vec![write_index];
        indices.extend(
            property_indices
                .iter()
                .filter(|(candidate_index_sort, candidate_value_sort, _)| {
                    candidate_index_sort == index_sort && candidate_value_sort == value_sort
                })
                .map(|(_, _, index)| index.clone()),
        );
        for index in indices {
            let trigger =
                ArrayLanguage::read_typed(index_sort, value_sort, expression.clone(), index);
            triggers.insert(expr_to_term(trigger));
        }
    }
    let mut triggers = triggers.into_iter().collect::<Vec<_>>();
    triggers.sort_by_key(ToString::to_string);
    triggers
}

fn expression_at(expression: &ArrayExpr, root: egg::Id) -> ArrayExpr {
    expression[root].build_recexpr(|id| expression[id].clone())
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
        depth: u16,
    ) -> anyhow::Result<ArrayEGraphBuildStep> {
        match self.stage {
            ConeThenFullStage::Cone => {
                let subterms = smt.get_all_subterms();
                let total_subterms = subterms.len();
                let dynamic_terms =
                    property_cone
                        .provenance
                        .demand_frontier(depth, smt)
                        .map(|frontier| {
                            let site_count = frontier.sites().len();
                            (
                                frontier.expressions().cloned().collect::<HashSet<_>>(),
                                site_count,
                            )
                        });
                let (cone_terms, demand_frontier_sites) = match dynamic_terms {
                    Ok((terms, site_count)) if !terms.is_empty() => (terms, site_count),
                    Ok(_) => (static_cone_terms(property_cone, &subterms), 0),
                    Err(error) => {
                        log::warn!(
                            "dynamic array demand frontier failed at depth {depth}: {error:#}; using the static cone"
                        );
                        (static_cone_terms(property_cone, &subterms), 0)
                    }
                };
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
                        candidate_scope: CandidateScope::AllCandidates,
                        total_subterms,
                        admitted_subterms: self.admitted.len(),
                        newly_admitted_subterms,
                        demand_frontier_sites: 0,
                    }));
                }

                self.stage = ConeThenFullStage::Full;
                let newly_admitted_subterms =
                    add_subterms(egraph, smt, &cone_refs, &mut self.admitted)?;
                egraph.rebuild();
                Ok(ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
                    stage: ArrayEGraphBuildStage::Cone,
                    candidate_scope: CandidateScope::SourceGroundedOnly,
                    total_subterms,
                    admitted_subterms: self.admitted.len(),
                    newly_admitted_subterms,
                    demand_frontier_sites,
                }))
            }
            ConeThenFullStage::Full => {
                self.stage = ConeThenFullStage::Exhausted;
                let subterms = smt.get_all_subterms();
                let total_subterms = subterms.len();
                let newly_admitted_subterms =
                    add_subterms(egraph, smt, &subterms, &mut self.admitted)?;
                egraph.rebuild();
                Ok(ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
                    stage: ArrayEGraphBuildStage::Full,
                    candidate_scope: CandidateScope::AllCandidates,
                    total_subterms,
                    admitted_subterms: self.admitted.len(),
                    newly_admitted_subterms,
                    demand_frontier_sites: 0,
                }))
            }
            ConeThenFullStage::Exhausted => Ok(ArrayEGraphBuildStep::Exhausted),
        }
    }
}

fn static_cone_terms(property_cone: &PropertyCone, subterms: &[&Term]) -> HashSet<Term> {
    let cone_symbols = property_cone
        .array_states
        .iter()
        .cloned()
        .collect::<HashSet<_>>();
    cone_admitted_subterms(subterms, &cone_symbols)
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
        Term::Lambda { term, .. }
        | Term::Forall { term, .. }
        | Term::Exists { term, .. }
        | Term::Attributes { term, .. } => term_contains_cone_symbol(term, cone_symbols),
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
        Term::Lambda { term, .. }
        | Term::Forall { term, .. }
        | Term::Exists { term, .. }
        | Term::Attributes { term, .. } => collect_term_dependencies(term, admitted),
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
    use smt2parser::vmt::{variable::Variable, ReadsAndWrites};

    use crate::problem_context::ArrayCandidatePool;
    use crate::utils::SolverStatistics;

    struct FakeContext {
        terms: Vec<Term>,
        source_term_count: usize,
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

        fn get_source_subterms(&self) -> Vec<&Term> {
            self.terms.iter().take(self.source_term_count).collect()
        }

        fn get_solver_statistics(&self) -> SolverStatistics {
            SolverStatistics::default()
        }

        fn get_reason_unknown(&self) -> Option<String> {
            None
        }

        fn add_instantiation(
            &mut self,
            _request: crate::instantiation_provenance::InstantiationRequest,
        ) -> crate::instantiation_provenance::InstantiationInstallResult {
            Default::default()
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

        fn get_number_instantiation_assertions_added(&self) -> u64 {
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
    fn cone_admission_traverses_lambda_bodies() {
        let lambda: Term = "(lambda ((i Int)) (Read_Int_Int a@3 i))".parse().unwrap();
        let subterms = vec![&lambda];

        let admitted = cone_admitted_subterms(&subterms, &HashSet::from(["a".to_string()]));

        assert!(admitted.contains(&lambda));
        assert!(admitted.iter().any(|term| term.to_string() == "a@3"));
        assert!(admitted.iter().any(|term| term.to_string() == "i"));
    }

    #[test]
    fn cone_then_full_expands_the_same_egraph_before_exhaustion() {
        let context = FakeContext {
            terms: vec![
                "(Read_Int_Int a@3 i@3)".parse().unwrap(),
                "(Read_Int_Int b@3 j@3)".parse().unwrap(),
            ],
            source_term_count: 2,
        };
        let cone = PropertyCone {
            array_states: HashSet::from(["a".to_string()]),
            ..PropertyCone::default()
        };
        let mut builder = ConeThenFullEGraphBuilder::default();
        let mut egraph = egg::EGraph::new(());

        let first = builder.expand(&mut egraph, &context, &cone, 3).unwrap();
        let classes_after_cone = egraph.number_of_classes();
        let second = builder.expand(&mut egraph, &context, &cone, 3).unwrap();
        let classes_after_full = egraph.number_of_classes();
        let third = builder.expand(&mut egraph, &context, &cone, 3).unwrap();

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
                candidate_scope: CandidateScope::AllCandidates,
                ..
            })
        ));
        assert_eq!(third, ArrayEGraphBuildStep::Exhausted);
        assert!(classes_after_full > classes_after_cone);
    }

    #[test]
    fn full_builder_admits_every_term_in_one_expansion() {
        let context = FakeContext {
            terms: vec![
                "(Read_Int_Int a@3 i@3)".parse().unwrap(),
                "(Read_Int_Int b@3 j@3)".parse().unwrap(),
            ],
            source_term_count: 1,
        };
        let mut builder = FullEGraphBuilder::default();
        let mut egraph = egg::EGraph::new(());

        let first = builder
            .expand(&mut egraph, &context, &PropertyCone::default(), 3)
            .unwrap();
        let classes_after_full = egraph.number_of_classes();
        let second = builder
            .expand(&mut egraph, &context, &PropertyCone::default(), 3)
            .unwrap();

        assert!(matches!(
            first,
            ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
                candidate_scope: CandidateScope::AllCandidates,
                newly_admitted_subterms: 2,
                ..
            })
        ));
        assert_eq!(second, ArrayEGraphBuildStep::Exhausted);
        assert!(classes_after_full > 0);
    }

    #[test]
    fn source_then_full_builder_widens_the_same_egraph() {
        let context = FakeContext {
            terms: vec![
                "(Read_Int_Int a@3 i@3)".parse().unwrap(),
                "(Read_Int_Int b@3 j@3)".parse().unwrap(),
            ],
            source_term_count: 1,
        };
        let mut builder = SourceThenFullEGraphBuilder::default();
        let mut egraph = egg::EGraph::new(());

        let first = builder
            .expand(&mut egraph, &context, &PropertyCone::default(), 3)
            .unwrap();
        let classes_after_source = egraph.number_of_classes();
        let second = builder
            .expand(&mut egraph, &context, &PropertyCone::default(), 3)
            .unwrap();
        let classes_after_full = egraph.number_of_classes();
        let third = builder
            .expand(&mut egraph, &context, &PropertyCone::default(), 3)
            .unwrap();

        assert!(matches!(
            first,
            ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
                stage: ArrayEGraphBuildStage::Source,
                candidate_scope: CandidateScope::SourceGroundedOnly,
                newly_admitted_subterms: 1,
                ..
            })
        ));
        assert!(matches!(
            second,
            ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
                stage: ArrayEGraphBuildStage::Full,
                candidate_scope: CandidateScope::AllCandidates,
                newly_admitted_subterms: 1,
                ..
            })
        ));
        assert_eq!(third, ArrayEGraphBuildStep::Exhausted);
        assert!(classes_after_full > classes_after_source);
    }

    #[test]
    fn source_then_full_builder_widens_across_setup_clones_at_one_depth() {
        let context = FakeContext {
            terms: vec![
                "(Read_Int_Int a@3 i@3)".parse().unwrap(),
                "(Read_Int_Int b@3 j@3)".parse().unwrap(),
            ],
            source_term_count: 1,
        };
        let template = SourceThenFullEGraphBuilder::default();
        let mut attempted_depths = HashSet::new();

        let mut source_builder = template.clone_for_refinement(&mut attempted_depths, 3);
        let mut source_egraph = egg::EGraph::new(());
        let source = source_builder
            .expand(&mut source_egraph, &context, &PropertyCone::default(), 3)
            .unwrap();

        assert!(!template.should_widen_after_source(2));
        assert!(template.should_widen_after_source(1));
        attempted_depths.insert(3);

        let mut full_builder = template.clone_for_refinement(&mut attempted_depths, 3);
        let mut full_egraph = egg::EGraph::new(());
        let full = full_builder
            .expand(&mut full_egraph, &context, &PropertyCone::default(), 3)
            .unwrap();

        assert!(matches!(
            source,
            ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
                stage: ArrayEGraphBuildStage::Source,
                candidate_scope: CandidateScope::SourceGroundedOnly,
                ..
            })
        ));
        assert!(matches!(
            full,
            ArrayEGraphBuildStep::Expanded(ArrayEGraphExpansion {
                stage: ArrayEGraphBuildStage::Full,
                candidate_scope: CandidateScope::AllCandidates,
                ..
            })
        ));
    }

    #[test]
    fn source_writes_seed_read_after_write_and_property_index_triggers() {
        let catalog = ArrayCandidateCatalog {
            source_grounded: ArrayCandidatePool {
                terms: vec!["(Write_Int_Int A i v)".to_string()],
                reads_and_writes: ReadsAndWrites::default(),
            },
            derived: ArrayCandidatePool::default(),
        };

        assert_eq!(
            source_array_axiom_triggers(&catalog, &["(Read_Int_Int A p)".to_string()]),
            vec![
                "(Read_Int_Int (Write_Int_Int A i v) i)"
                    .parse::<Term>()
                    .unwrap(),
                "(Read_Int_Int (Write_Int_Int A i v) p)"
                    .parse::<Term>()
                    .unwrap(),
            ]
        );
    }
}
