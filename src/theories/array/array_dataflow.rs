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
    concrete::{QualIdentifier, Term},
    vmt::{
        bmc::BMCBuilder,
        definition_graph::{DefinitionFrameInfo, DefinitionGraph},
        VMTModel,
    },
};

use crate::problem_context::ProblemContext;

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

/// A Boolean condition required for a particular update path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GuardedPathCondition {
    pub expression: Term,
    pub required_value: bool,
}

/// One guarded definition of a next-state variable.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StateUpdatePath {
    /// Current-state name for the variable being defined.
    pub target: String,
    /// Exact next-state expression appearing in the transition relation.
    pub target_expression: Term,
    /// Exact expression assigned to the target on this path.
    pub value: Term,
    pub guards: Vec<GuardedPathCondition>,
    pub dependencies: Vec<ExpressionSite>,
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
    property: Term,
    property_sites: Vec<ExpressionSite>,
    updates: BTreeMap<String, Vec<StateUpdatePath>>,
    current_variables: Vec<String>,
    array_variables: HashSet<String>,
    next_to_current: std::collections::HashMap<String, String>,
    definition_frames: DefinitionFrameInfo,
}

impl Default for StaticArrayProvenance {
    fn default() -> Self {
        Self {
            property: Term::QualIdentifier(QualIdentifier::simple("true")),
            property_sites: Vec::new(),
            updates: BTreeMap::new(),
            current_variables: Vec::new(),
            array_variables: HashSet::new(),
            next_to_current: std::collections::HashMap::new(),
            definition_frames: DefinitionFrameInfo::default(),
        }
    }
}

impl StaticArrayProvenance {
    pub fn from_model(model: &VMTModel) -> Self {
        let graph = model.get_helper_definitions();
        let current_variable_names = model.get_all_current_variable_names();
        let next_to_current = model.get_next_to_current_varible_names();
        let array_variables = model
            .get_state_variables()
            .into_iter()
            .filter(|variable| variable.get_sort_name().contains("Array"))
            .map(|variable| variable.get_current_variable_name().clone())
            .collect();
        let definition_frames =
            DefinitionFrameInfo::new(graph, &current_variable_names, &next_to_current);
        let property = model.get_property_for_yardbird();
        let mut builder = ProvenanceBuilder {
            graph,
            next_to_current: next_to_current.clone(),
        };
        let property_sites =
            builder.expression_sites(&property, DataflowRole::PropertyControlDependency);
        let mut updates = BTreeMap::<String, Vec<StateUpdatePath>>::new();
        builder.collect_updates(
            &model.get_trans_condition_for_yardbird(),
            &[],
            &mut HashSet::new(),
            &mut updates,
        );

        Self {
            property,
            property_sites,
            updates,
            current_variables: current_variable_names,
            array_variables,
            next_to_current,
            definition_frames,
        }
    }

    pub fn property(&self) -> &Term {
        &self.property
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
        let mut sites = BTreeMap::<(String, DataflowRole), FramedDemandSite>::new();
        let mut queue = VecDeque::<(String, u16, DataflowRole)>::new();
        let mut visited = HashSet::<(String, u16, DataflowRole)>::new();
        let mut guard_values = std::collections::HashMap::<Term, bool>::new();

        for site in &self.property_sites {
            let expression = self.index_term(&site.expression, depth);
            insert_framed_site(&mut sites, expression, site.role);
            if let Some(state) =
                leaf_symbol(&site.expression).filter(|state| self.current_variables.contains(state))
            {
                queue.push_back((state, depth, site.role));
            }
        }

        while let Some((state, target_frame, demanded_role)) = queue.pop_front() {
            if target_frame == 0 || !visited.insert((state.clone(), target_frame, demanded_role)) {
                continue;
            }
            let transition_frame = target_frame - 1;
            for path in self.update_paths(&state) {
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
        let mut builder = BMCBuilder::with_definition_frames(
            self.current_variables.clone(),
            self.next_to_current.clone(),
            self.definition_frames.clone(),
        );
        builder.set_depth(depth);
        builder.index_single_step_term(term.clone())
    }
}

pub fn build_property_cone(model: &VMTModel) -> PropertyCone {
    StaticArrayProvenance::from_model(model).property_cone()
}

struct ProvenanceBuilder<'a> {
    graph: &'a DefinitionGraph,
    next_to_current: std::collections::HashMap<String, String>,
}

impl ProvenanceBuilder<'_> {
    fn collect_updates(
        &mut self,
        term: &Term,
        guards: &[GuardedPathCondition],
        active_helpers: &mut HashSet<String>,
        updates: &mut BTreeMap<String, Vec<StateUpdatePath>>,
    ) {
        if let Some(symbol) = leaf_symbol(term) {
            if let Some(definition) = self.graph.get(&symbol) {
                if active_helpers.insert(symbol.clone()) {
                    self.collect_updates(definition.body(), guards, active_helpers, updates);
                    active_helpers.remove(&symbol);
                }
            }
            return;
        }

        let Term::Application {
            qual_identifier,
            arguments,
        } = term
        else {
            return;
        };

        match qual_identifier.get_name().as_str() {
            "=>" if arguments.len() == 2 => {
                let mut nested_guards = guards.to_vec();
                nested_guards.push(GuardedPathCondition {
                    expression: arguments[0].clone(),
                    required_value: true,
                });
                self.collect_updates(&arguments[1], &nested_guards, active_helpers, updates);
            }
            "ite" if arguments.len() == 3 => {
                let condition = arguments[0].clone();
                for (required_value, branch) in [(true, &arguments[1]), (false, &arguments[2])] {
                    let mut nested_guards = guards.to_vec();
                    nested_guards.push(GuardedPathCondition {
                        expression: condition.clone(),
                        required_value,
                    });
                    self.collect_updates(branch, &nested_guards, active_helpers, updates);
                }
            }
            "or" => {
                for branch in arguments {
                    let mut nested_guards = guards.to_vec();
                    nested_guards.push(GuardedPathCondition {
                        expression: branch.clone(),
                        required_value: true,
                    });
                    self.collect_updates(branch, &nested_guards, active_helpers, updates);
                }
            }
            "=" if arguments.len() == 2 => {
                if let Some((target, target_expression, value)) =
                    self.state_update(&arguments[0], &arguments[1])
                {
                    self.record_update_paths(target, target_expression, value, guards, updates);
                }
            }
            _ => {
                for argument in arguments {
                    self.collect_updates(argument, guards, active_helpers, updates);
                }
            }
        }
    }

    fn record_update_paths(
        &self,
        target: String,
        target_expression: Term,
        value: Term,
        guards: &[GuardedPathCondition],
        updates: &mut BTreeMap<String, Vec<StateUpdatePath>>,
    ) {
        let expanded_value = self.expand_leaf_helper(&value);
        if let Term::Application {
            qual_identifier,
            arguments,
        } = &expanded_value
        {
            if qual_identifier.get_name() == "ite" && arguments.len() == 3 {
                for (required_value, branch) in
                    [(true, arguments[1].clone()), (false, arguments[2].clone())]
                {
                    let mut nested_guards = guards.to_vec();
                    nested_guards.push(GuardedPathCondition {
                        expression: arguments[0].clone(),
                        required_value,
                    });
                    self.record_update_paths(
                        target.clone(),
                        target_expression.clone(),
                        branch,
                        &nested_guards,
                        updates,
                    );
                }
                return;
            }
        }

        let mut dependencies =
            self.expression_sites(&expanded_value, DataflowRole::ScalarUpdateDependency);
        for guard in guards {
            dependencies.extend(
                self.expression_sites(&guard.expression, DataflowRole::PropertyControlDependency),
            );
        }
        deduplicate_sites(&mut dependencies);
        updates
            .entry(target.clone())
            .or_default()
            .push(StateUpdatePath {
                target,
                target_expression,
                value: expanded_value,
                guards: guards.to_vec(),
                dependencies,
            });
    }

    fn state_update(&self, left: &Term, right: &Term) -> Option<(String, Term, Term)> {
        if let Some(target) = self.next_state_target(left) {
            return Some((target, left.clone(), self.expand_leaf_helper(right)));
        }
        self.next_state_target(right)
            .map(|target| (target, right.clone(), self.expand_leaf_helper(left)))
    }

    fn next_state_target(&self, term: &Term) -> Option<String> {
        leaf_symbol(term).and_then(|symbol| self.next_to_current.get(&symbol).cloned())
    }

    fn expand_leaf_helper(&self, term: &Term) -> Term {
        let mut expanded = term.clone();
        let mut active_helpers = HashSet::new();
        while let Some(symbol) = leaf_symbol(&expanded) {
            let Some(definition) = self.graph.get(&symbol) else {
                break;
            };
            if !active_helpers.insert(symbol) {
                break;
            }
            expanded = definition.body().clone();
        }
        expanded
    }

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
            Term::Forall { term, .. }
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

fn leaf_symbol(term: &Term) -> Option<String> {
    match term {
        Term::QualIdentifier(identifier) => Some(identifier.get_name()),
        Term::Application {
            qual_identifier,
            arguments,
        } if arguments.is_empty() => Some(qual_identifier.get_name()),
        _ => None,
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
    use smt2parser::vmt::{quantified_instantiator::Instance, variable::Variable, ReadsAndWrites};

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
            _inst: Instance,
            _abstract_instantiation_id: Option<String>,
        ) -> bool {
            false
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
            Ok((rendered.contains("(= pc@0 0)") && !rendered.contains("(= pc@0 1)")).to_string())
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
            _inst: Instance,
            _abstract_instantiation_id: Option<String>,
        ) -> bool {
            false
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
