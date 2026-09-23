//! Static provenance and model-specific demand for array refinement.
//!
//! This module records exact VMT expression sites. It deliberately does not
//! turn sites into normalized term patterns or enumerate framed copies. A
//! dynamic demand walk selects active guarded update paths and indexes their
//! sites at the exact BMC frame where they are needed.
//!
//! Frame-offset and dataflow-distance metadata are intentionally omitted until
//! a ranker consumes them. The extension point is `ExpressionSite` for static
//! metadata and `FramedDemandSite`/`insert_framed_site` for dynamic metadata.

use std::collections::{BTreeMap, HashSet, VecDeque};

use smt2parser::{
    concrete::Term,
    vmt::{definition_graph::DefinitionGraph, VMTModel},
};

use crate::problem_context::ProblemContext;
use crate::transition_index::{
    leaf_symbol, StateUpdatePath as TransitionUpdatePath, TransitionIndex,
};
use std::sync::Arc;

/// The role an exact expression site plays in array/scalar dataflow.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DataflowRole {
    ArrayLineage,
    WriteIndex,
    WriteValue,
    DemandedReadIndex,
    ScalarUpdateDependency,
    PropertyControlDependency,
}

/// An expression at its original VMT source site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpressionSite {
    pub expression: Term,
    pub role: DataflowRole,
}

/// Array-specific expression roles over the shared transition update.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StateUpdatePath {
    pub update: TransitionUpdatePath,
    pub dependencies: Vec<ExpressionSite>,
}

impl std::ops::Deref for StateUpdatePath {
    type Target = TransitionUpdatePath;
    fn deref(&self) -> &Self::Target {
        &self.update
    }
}

/// One exact, framed expression reached by the current model's demand walk.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FramedDemandSite {
    pub expression: Term,
    pub role: DataflowRole,
}

#[derive(Clone, Debug, Default)]
pub struct PropertyCone {
    pub array_states: HashSet<String>,
    pub provenance: StaticArrayProvenance,
}

/// The lazily explored dataflow cone for one counterexample model.
#[derive(Clone, Debug, Default)]
pub struct DemandFrontier {
    sites: Vec<FramedDemandSite>,
}

impl DemandFrontier {
    pub fn sites(&self) -> &[FramedDemandSite] {
        &self.sites
    }

    pub fn expressions(&self) -> impl Iterator<Item = &Term> {
        self.sites.iter().map(|site| &site.expression)
    }
}

/// Static provenance needed to construct model-specific demand frontiers.
#[derive(Clone, Debug)]
pub struct StaticArrayProvenance {
    transitions: Arc<TransitionIndex>,
    action_sites: BTreeMap<String, Vec<ExpressionSite>>,
    property_sites: Vec<ExpressionSite>,
    updates: BTreeMap<String, Vec<StateUpdatePath>>,
    current_variables: Vec<String>,
    array_variables: HashSet<String>,
}

impl Default for StaticArrayProvenance {
    fn default() -> Self {
        Self {
            transitions: Arc::new(TransitionIndex::default()),
            action_sites: BTreeMap::new(),
            property_sites: Vec::new(),
            updates: BTreeMap::new(),
            current_variables: Vec::new(),
            array_variables: HashSet::new(),
        }
    }
}

impl StaticArrayProvenance {
    pub fn from_model(model: &VMTModel) -> Self {
        Self::with_transition_index(
            model,
            Arc::new(TransitionIndex::from_model(model, &HashSet::new())),
        )
    }

    pub fn with_transition_index(model: &VMTModel, transitions: Arc<TransitionIndex>) -> Self {
        let builder = ProvenanceBuilder {
            graph: model.get_helper_definitions(),
        };
        let property_sites = builder.expression_sites(
            transitions.property(),
            DataflowRole::PropertyControlDependency,
        );
        let mut updates = BTreeMap::<String, Vec<StateUpdatePath>>::new();
        for update in transitions.updates() {
            let mut dependencies =
                builder.expression_sites(&update.value, DataflowRole::ScalarUpdateDependency);
            for guard in &update.guards {
                dependencies.extend(
                    builder.expression_sites(
                        &guard.expression,
                        DataflowRole::PropertyControlDependency,
                    ),
                );
            }
            deduplicate_sites(&mut dependencies);
            updates
                .entry(update.target.clone())
                .or_default()
                .push(StateUpdatePath {
                    update: update.clone(),
                    dependencies,
                });
        }
        let action_sites = transitions
            .actions()
            .iter()
            .map(|(name, action)| {
                let mut sites = action
                    .requirements
                    .iter()
                    .flat_map(|r| {
                        builder.expression_sites(&r.body, DataflowRole::PropertyControlDependency)
                    })
                    .collect();
                deduplicate_sites(&mut sites);
                (name.clone(), sites)
            })
            .collect();
        Self {
            transitions,
            action_sites,
            property_sites,
            updates,
            current_variables: model.get_all_current_variable_names(),
            array_variables: model
                .get_state_variables()
                .into_iter()
                .filter(|v| v.get_sort_name().contains("Array"))
                .map(|v| v.get_current_variable_name().clone())
                .collect(),
        }
    }

    pub fn transition_index(&self) -> &TransitionIndex {
        &self.transitions
    }

    pub fn action_sites(&self, action: &str) -> &[ExpressionSite] {
        self.action_sites
            .get(action)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    pub fn property(&self) -> &Term {
        self.transitions.property()
    }

    pub fn property_sites(&self) -> &[ExpressionSite] {
        &self.property_sites
    }

    pub fn update_paths(&self, current_state: &str) -> &[StateUpdatePath] {
        self.updates
            .get(current_state)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    pub fn updated_states(&self) -> impl Iterator<Item = &str> {
        self.updates.keys().map(String::as_str)
    }

    pub fn property_cone(&self) -> PropertyCone {
        let current_variables = self.current_variables.iter().collect::<HashSet<_>>();
        let mut states = HashSet::<String>::new();
        let mut queue = VecDeque::<String>::new();

        for site in &self.property_sites {
            let Some(state) = leaf_symbol(&site.expression) else {
                continue;
            };
            if current_variables.contains(&state) && states.insert(state.clone()) {
                queue.push_back(state);
            }
        }

        while let Some(state) = queue.pop_front() {
            for path in self.update_paths(&state) {
                for site in &path.dependencies {
                    let Some(dependency) = leaf_symbol(&site.expression) else {
                        continue;
                    };
                    if current_variables.contains(&dependency) && states.insert(dependency.clone())
                    {
                        queue.push_back(dependency);
                    }
                }
            }
        }

        let array_states = states
            .into_iter()
            .filter(|state| self.array_variables.contains(state))
            .collect();
        PropertyCone {
            array_states,
            provenance: self.clone(),
        }
    }

    /// Follow exact state-update paths whose guards are active in `smt`'s
    /// current model. Passthrough updates such as `sum' = sum` are traversed
    /// without admitting every intermediate framed copy of `sum`.
    pub fn demand_frontier(
        &self,
        depth: u16,
        smt: &dyn ProblemContext,
    ) -> anyhow::Result<DemandFrontier> {
        let roots = self
            .property_sites
            .iter()
            .map(|site| FramedDemandSite {
                expression: self.index_term(&site.expression, depth),
                role: site.role,
            })
            .collect::<Vec<_>>();
        self.walk_demand(roots, smt)
    }

    /// Seed the same action-aware traversal with already-ground, already-framed
    /// reads exposed by property binder witnesses. No frame shifting is applied
    /// to the supplied terms (their captures may refer to different frames).
    pub fn demand_frontier_from_terms(
        &self,
        terms: &[Term],
        smt: &dyn ProblemContext,
    ) -> anyhow::Result<DemandFrontier> {
        let graph = DefinitionGraph::default();
        let builder = ProvenanceBuilder { graph: &graph };
        let roots = terms
            .iter()
            .flat_map(|term| {
                builder.expression_sites(term, DataflowRole::PropertyControlDependency)
            })
            .map(|site| FramedDemandSite {
                expression: site.expression,
                role: site.role,
            })
            .collect();
        self.walk_demand(roots, smt)
    }

    fn walk_demand(
        &self,
        roots: Vec<FramedDemandSite>,
        smt: &dyn ProblemContext,
    ) -> anyhow::Result<DemandFrontier> {
        let mut sites = BTreeMap::<(String, DataflowRole), FramedDemandSite>::new();
        let mut queue = VecDeque::<(String, u16, DataflowRole)>::new();
        let mut visited = HashSet::<(String, u16, DataflowRole)>::new();
        let mut guard_values = std::collections::HashMap::<Term, bool>::new();
        let mut selected_actions = BTreeMap::new();
        for site in roots {
            if let Some((state, frame)) =
                leaf_symbol(&site.expression).and_then(|s| smt2parser::vmt::split_framed_symbol(&s))
            {
                if self.current_variables.contains(&state) {
                    queue.push_back((
                        state,
                        u16::try_from(frame)
                            .map_err(|_| anyhow::anyhow!("unsupported demand frame {frame}"))?,
                        site.role,
                    ));
                }
            }
            insert_framed_site(&mut sites, site.expression, site.role);
        }

        while let Some((state, target_frame, demanded_role)) = queue.pop_front() {
            if target_frame == 0 || !visited.insert((state.clone(), target_frame, demanded_role)) {
                continue;
            }
            let transition_frame = target_frame - 1;
            let selected = if let Some(selected) = selected_actions.get(&transition_frame) {
                selected
            } else {
                let selected = self
                    .transitions
                    .selected_action(transition_frame, |t| smt.eval_to_string(t))?
                    .map(str::to_owned);
                selected_actions.entry(transition_frame).or_insert(selected)
            };
            for path in self.update_paths(&state) {
                if path
                    .action
                    .as_ref()
                    .is_some_and(|action| Some(action) != selected.as_ref())
                {
                    continue;
                }
                if !self.path_is_active(path, transition_frame, smt, &mut guard_values)? {
                    continue;
                }

                if is_passthrough(&path.value, &state) {
                    queue.push_back((state.clone(), transition_frame, demanded_role));
                    continue;
                }

                insert_framed_site(
                    &mut sites,
                    self.index_term(&path.target_expression, transition_frame),
                    demanded_role,
                );

                for dependency in &path.dependencies {
                    let indexed = self.index_term(&dependency.expression, transition_frame);
                    insert_framed_site(&mut sites, indexed, dependency.role);

                    if dependency.role == DataflowRole::PropertyControlDependency {
                        continue;
                    }
                    if let Some(source) = leaf_symbol(&dependency.expression)
                        .filter(|source| self.current_variables.contains(source))
                    {
                        queue.push_back((source, transition_frame, dependency.role));
                    }
                }
            }
        }

        Ok(DemandFrontier {
            sites: sites.into_values().collect(),
        })
    }

    fn path_is_active(
        &self,
        path: &StateUpdatePath,
        transition_frame: u16,
        smt: &dyn ProblemContext,
        guard_values: &mut std::collections::HashMap<Term, bool>,
    ) -> anyhow::Result<bool> {
        for guard in &path.guards {
            let indexed = self.index_term(&guard.expression, transition_frame);
            let actual = match guard_values.get(&indexed) {
                Some(actual) => *actual,
                None => {
                    let value = smt.eval_to_string(&indexed)?;
                    let actual = match value.trim() {
                        "true" => true,
                        "false" => false,
                        other => anyhow::bail!(
                            "expected Boolean model value for dataflow guard {indexed}, got {other}"
                        ),
                    };
                    guard_values.insert(indexed, actual);
                    actual
                }
            };
            if actual != guard.required_value {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn index_term(&self, term: &Term, depth: u16) -> Term {
        self.transitions.index_term(term, depth)
    }
}

pub fn build_property_cone(model: &VMTModel) -> PropertyCone {
    StaticArrayProvenance::from_model(model).property_cone()
}

struct ProvenanceBuilder<'a> {
    graph: &'a DefinitionGraph,
}

impl ProvenanceBuilder<'_> {
    fn expression_sites(&self, term: &Term, role: DataflowRole) -> Vec<ExpressionSite> {
        let mut sites = Vec::new();
        self.collect_expression_sites(term, role, &mut HashSet::new(), &mut sites);
        deduplicate_sites(&mut sites);
        sites
    }

    fn collect_expression_sites(
        &self,
        term: &Term,
        role: DataflowRole,
        active_helpers: &mut HashSet<String>,
        sites: &mut Vec<ExpressionSite>,
    ) {
        sites.push(ExpressionSite {
            expression: term.clone(),
            role,
        });

        if let Some(symbol) = leaf_symbol(term) {
            if let Some(definition) = self.graph.get(&symbol) {
                if active_helpers.insert(symbol.clone()) {
                    self.collect_expression_sites(definition.body(), role, active_helpers, sites);
                    active_helpers.remove(&symbol);
                }
            }
            return;
        }

        match term {
            Term::Application {
                qual_identifier,
                arguments,
            } => match qual_identifier.get_name().as_str() {
                "select" if arguments.len() == 2 => {
                    self.collect_expression_sites(
                        &arguments[0],
                        DataflowRole::ArrayLineage,
                        active_helpers,
                        sites,
                    );
                    self.collect_expression_sites(
                        &arguments[1],
                        DataflowRole::DemandedReadIndex,
                        active_helpers,
                        sites,
                    );
                }
                name if name.starts_with("Read_") && arguments.len() == 2 => {
                    self.collect_expression_sites(
                        &arguments[0],
                        DataflowRole::ArrayLineage,
                        active_helpers,
                        sites,
                    );
                    self.collect_expression_sites(
                        &arguments[1],
                        DataflowRole::DemandedReadIndex,
                        active_helpers,
                        sites,
                    );
                }
                "store" if arguments.len() == 3 => {
                    self.collect_write_sites(arguments, active_helpers, sites);
                }
                name if name.starts_with("Write_") && arguments.len() == 3 => {
                    self.collect_write_sites(arguments, active_helpers, sites);
                }
                _ => {
                    for argument in arguments {
                        self.collect_expression_sites(argument, role, active_helpers, sites);
                    }
                }
            },
            Term::Let { var_bindings, term } => {
                for (_, value) in var_bindings {
                    self.collect_expression_sites(value, role, active_helpers, sites);
                }
                self.collect_expression_sites(term, role, active_helpers, sites);
            }
            Term::Lambda { term, .. }
            | Term::Forall { term, .. }
            | Term::Exists { term, .. }
            | Term::Attributes { term, .. } => {
                self.collect_expression_sites(term, role, active_helpers, sites);
            }
            Term::Match { term, cases } => {
                self.collect_expression_sites(term, role, active_helpers, sites);
                for (_, case) in cases {
                    self.collect_expression_sites(case, role, active_helpers, sites);
                }
            }
            Term::Constant(_) | Term::QualIdentifier(_) => {}
        }
    }

    fn collect_write_sites(
        &self,
        arguments: &[Term],
        active_helpers: &mut HashSet<String>,
        sites: &mut Vec<ExpressionSite>,
    ) {
        self.collect_expression_sites(
            &arguments[0],
            DataflowRole::ArrayLineage,
            active_helpers,
            sites,
        );
        self.collect_expression_sites(
            &arguments[1],
            DataflowRole::WriteIndex,
            active_helpers,
            sites,
        );
        self.collect_expression_sites(
            &arguments[2],
            DataflowRole::WriteValue,
            active_helpers,
            sites,
        );
    }
}

fn deduplicate_sites(sites: &mut Vec<ExpressionSite>) {
    let mut seen = HashSet::new();
    sites.retain(|site| seen.insert((site.expression.clone(), site.role)));
}

fn is_passthrough(value: &Term, target: &str) -> bool {
    leaf_symbol(value).is_some_and(|source| source == target)
}

fn insert_framed_site(
    sites: &mut BTreeMap<(String, DataflowRole), FramedDemandSite>,
    expression: Term,
    role: DataflowRole,
) {
    let rendered = expression.to_string();
    let key = (rendered, role);
    sites
        .entry(key)
        .or_insert(FramedDemandSite { expression, role });
}

#[cfg(test)]
mod tests {
    use super::*;
    use smt2parser::vmt::{variable::Variable, ReadsAndWrites};

    use crate::utils::SolverStatistics;

    struct GuardModel;

    struct DisjunctionModel;

    impl ProblemContext for GuardModel {
        fn as_any(&self) -> &dyn std::any::Any {
            self
        }

        fn has_model(&self) -> bool {
            true
        }

        fn eval_to_string(&self, term: &Term) -> anyhow::Result<String> {
            let rendered = term.to_string();
            let active = if rendered.contains("(not (<") {
                false
            } else if rendered.contains("(= pc@2 3)") {
                true
            } else {
                rendered.contains("(= pc@") && rendered.contains(" 1)")
            };
            Ok(active.to_string())
        }

        fn model_to_string(&self) -> anyhow::Result<String> {
            Ok(String::new())
        }

        fn get_all_subterms(&self) -> Vec<&Term> {
            Vec::new()
        }

        fn get_solver_statistics(&self) -> SolverStatistics {
            SolverStatistics::default()
        }

        fn get_reason_unknown(&self) -> Option<String> {
            None
        }

        fn add_instantiation(
            &mut self,
            _request: crate::instance_installation::request::InstantiationRequest,
        ) -> crate::instance_installation::request::InstantiationInstallResult {
            Default::default()
        }

        fn get_instantiations(&self) -> Vec<Term> {
            Vec::new()
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
            Vec::new()
        }

        fn get_property_subterms(&self) -> Vec<String> {
            Vec::new()
        }

        fn get_reads_and_writes(&self) -> ReadsAndWrites {
            ReadsAndWrites::default()
        }

        fn get_array_types(&self) -> Vec<(String, String)> {
            Vec::new()
        }
    }

    impl ProblemContext for DisjunctionModel {
        fn as_any(&self) -> &dyn std::any::Any {
            self
        }

        fn has_model(&self) -> bool {
            true
        }

        fn eval_to_string(&self, term: &Term) -> anyhow::Result<String> {
            let rendered = term.to_string();
            Ok(
                ((rendered.contains("(= pc@0 0)") && !rendered.contains("(= pc@0 1)"))
                    || rendered == "send@1"
                    || rendered == "idle@0")
                    .to_string(),
            )
        }

        fn model_to_string(&self) -> anyhow::Result<String> {
            Ok(String::new())
        }

        fn get_all_subterms(&self) -> Vec<&Term> {
            Vec::new()
        }

        fn get_solver_statistics(&self) -> SolverStatistics {
            SolverStatistics::default()
        }

        fn get_reason_unknown(&self) -> Option<String> {
            None
        }

        fn add_instantiation(
            &mut self,
            _request: crate::instance_installation::request::InstantiationRequest,
        ) -> crate::instance_installation::request::InstantiationInstallResult {
            Default::default()
        }

        fn get_instantiations(&self) -> Vec<Term> {
            Vec::new()
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
            Vec::new()
        }

        fn get_property_subterms(&self) -> Vec<String> {
            Vec::new()
        }

        fn get_reads_and_writes(&self) -> ReadsAndWrites {
            ReadsAndWrites::default()
        }

        fn get_array_types(&self) -> Vec<(String, String)> {
            Vec::new()
        }
    }

    #[test]
    fn witness_demands_follow_the_selected_action_and_branch_without_reframing_captures() {
        let model = VMTModel::from_path("tests/fixtures/array_dataflow_actions.vmt").unwrap();
        let provenance = StaticArrayProvenance::from_model(&model);
        let witness_read: Term = "(select a@2 (witness a@0))".parse().unwrap();
        let frontier = provenance
            .demand_frontier_from_terms(std::slice::from_ref(&witness_read), &DisjunctionModel)
            .unwrap();
        assert!(frontier.expressions().any(|t| t == &witness_read));
        let indices = frontier
            .sites()
            .iter()
            .filter(|s| s.role == DataflowRole::WriteIndex)
            .map(|s| s.expression.to_string())
            .collect::<HashSet<_>>();
        assert_eq!(indices, HashSet::from(["2".into()]));
        assert!(frontier.expressions().any(|t| t.to_string() == "a@1"));
        assert!(!frontier.expressions().any(|t| t.to_string() == "b@2"));
        assert!(frontier
            .expressions()
            .any(|t| t.to_string() == "(witness a@0)"));
        // The original property traversal is still available and remains on b.
        let original = provenance.demand_frontier(2, &DisjunctionModel).unwrap();
        assert!(!original
            .sites()
            .iter()
            .any(|s| s.role == DataflowRole::WriteIndex));
    }

    #[test]
    fn expression_sites_traverse_lambda_bodies() {
        let graph = DefinitionGraph::default();
        let builder = ProvenanceBuilder { graph: &graph };
        let lambda: Term = "(lambda ((i Int)) (select A i))".parse().unwrap();

        let sites = builder.expression_sites(&lambda, DataflowRole::ScalarUpdateDependency);

        assert!(sites.iter().any(|site| {
            site.role == DataflowRole::ArrayLineage && site.expression.to_string() == "A"
        }));
        assert!(sites.iter().any(|site| {
            site.role == DataflowRole::DemandedReadIndex && site.expression.to_string() == "i"
        }));
    }

    fn has_site(path: &StateUpdatePath, expression: &str, role: DataflowRole) -> bool {
        path.dependencies
            .iter()
            .any(|site| site.expression.to_string() == expression && site.role == role)
    }

    #[test]
    fn records_exact_scalar_read_dependencies() {
        let model =
            VMTModel::from_path("examples/array/array_init_both_ends_multiple_sum.vmt").unwrap();
        let provenance = StaticArrayProvenance::from_model(&model);
        let sum_updates = provenance.update_paths("sum");
        let accumulating = sum_updates
            .iter()
            .find(|path| path.value.to_string().contains("(select a i)"))
            .expect("sum should have an update that consumes the array reads");

        assert_eq!(accumulating.target_expression.to_string(), "sum_next");
        assert!(has_site(
            accumulating,
            "sum",
            DataflowRole::ScalarUpdateDependency
        ));
        assert!(has_site(accumulating, "a", DataflowRole::ArrayLineage));
        assert!(has_site(accumulating, "i", DataflowRole::DemandedReadIndex));
    }

    #[test]
    fn static_cone_uses_the_same_provenance_graph_as_dynamic_demand() {
        let model = VMTModel::from_path("examples/array/array_copy.vmt").unwrap();
        let cone = build_property_cone(&model);

        assert!(cone.array_states.contains("b"));
        assert!(cone.array_states.contains("a"));
    }

    #[test]
    fn retains_separate_guarded_update_paths() {
        let model =
            VMTModel::from_path("examples/array/array_init_both_ends_multiple_sum.vmt").unwrap();
        let provenance = StaticArrayProvenance::from_model(&model);
        let sum_updates = provenance.update_paths("sum");

        assert!(sum_updates.len() >= 6);
        assert!(sum_updates.iter().any(|path| {
            path.guards.iter().any(|guard| {
                guard.required_value
                    && guard.expression.to_string().contains("(< i N)")
                    && guard.expression.to_string().contains("(= pc 3)")
            }) && path.value.to_string().contains("(select a i)")
        }));
        assert!(sum_updates.iter().any(|path| {
            path.guards.iter().any(|guard| {
                guard.required_value && guard.expression.to_string().contains("(not (< i N))")
            }) && path.value.to_string() == "sum"
        }));
    }

    #[test]
    fn property_read_sites_have_array_and_index_roles() {
        let model = VMTModel::from_path("examples/array/array_copy.vmt").unwrap();
        let provenance = StaticArrayProvenance::from_model(&model);

        assert!(provenance.property_sites().iter().any(|site| {
            site.expression.to_string() == "a" && site.role == DataflowRole::ArrayLineage
        }));
        assert!(provenance.property_sites().iter().any(|site| {
            site.expression.to_string() == "Z" && site.role == DataflowRole::DemandedReadIndex
        }));
    }

    #[test]
    fn dynamic_frontier_follows_active_paths_and_compresses_passthrough_frames() {
        let model =
            VMTModel::from_path("examples/array/array_init_both_ends_multiple_sum.vmt").unwrap();
        let provenance = StaticArrayProvenance::from_model(&model);
        let frontier = provenance.demand_frontier(6, &GuardModel).unwrap();
        let scalar_terms = frontier
            .sites()
            .iter()
            .filter(|site| site.role == DataflowRole::ScalarUpdateDependency)
            .map(|site| site.expression.to_string())
            .collect::<HashSet<_>>();

        assert!(scalar_terms.contains("sum@2"));
        assert!(frontier.sites().iter().any(|site| {
            site.expression.to_string().contains("(select a@2 i@2)")
                && site.role == DataflowRole::ScalarUpdateDependency
        }));
        assert!(!scalar_terms.contains("sum@5"));
        assert!(!scalar_terms.contains("sum@4"));
    }

    #[test]
    fn dynamic_frontier_ignores_updates_from_inactive_disjuncts() {
        let model = VMTModel::from_path("tests/fixtures/array_dataflow_disjunction.vmt").unwrap();
        let provenance = StaticArrayProvenance::from_model(&model);
        let frontier = provenance.demand_frontier(1, &DisjunctionModel).unwrap();
        let write_indices = frontier
            .sites()
            .iter()
            .filter(|site| site.role == DataflowRole::WriteIndex)
            .map(|site| site.expression.to_string())
            .collect::<HashSet<_>>();

        assert!(write_indices.contains("i@0"));
        assert!(!write_indices.contains("j@0"));
    }

    #[test]
    fn dynamic_frontier_fully_expands_helper_chains_before_selecting_active_path() {
        let model = VMTModel::from_path("tests/fixtures/array_dataflow_nested_helper.vmt").unwrap();
        let provenance = StaticArrayProvenance::from_model(&model);
        let frontier = provenance.demand_frontier(1, &DisjunctionModel).unwrap();
        let write_indices = frontier
            .sites()
            .iter()
            .filter(|site| site.role == DataflowRole::WriteIndex)
            .map(|site| site.expression.to_string())
            .collect::<HashSet<_>>();

        assert!(write_indices.contains("i@0"));
        assert!(!write_indices.contains("j@0"));
    }
}
