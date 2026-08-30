pub mod assertion_tracker;
pub mod full_unroll;
pub mod no_unroll_on_loop;
pub mod schema_batch;

use log::debug;
use smt2parser::{
    concrete::Term,
    vmt::{bmc::BMCBuilder, definition_materializer::DefinitionMaterializer},
};
use std::collections::HashSet;

use crate::{
    instantiation_provenance::{
        InstantiationInstallResult, InstantiationProvenance, InstantiationRequest,
        InstantiationSubstitution, StoredInstantiation,
    },
    instantiation_strategy::assertion_tracker::{AssertionKind, InstantiationAssertionTracker},
    solver::YardbirdSolver,
    subterm_handler::SubtermHandler,
    training::IndexedInstantiationRecord,
};

struct PreparedIndexedInstantiation {
    term: Term,
    frame: u16,
    substitution: Vec<InstantiationSubstitution>,
    provenance: Option<InstantiationProvenance>,
}

/// Owns the mechanics of installing theory instances into a BMC solver.
///
/// Instantiation strategies choose when existing instances are replayed. This
/// context keeps materialization, assertion deduplication, tracking labels, and
/// solver bookkeeping consistent across strategies.
pub struct InstantiationContext<'a> {
    instantiations: &'a mut Vec<StoredInstantiation>,
    bmc_builder: &'a mut BMCBuilder,
    definition_materializer: &'a mut DefinitionMaterializer,
    solver: &'a mut dyn YardbirdSolver,
    subterm_handler: &'a mut SubtermHandler,
    track_instantiations: bool,
    tracked_labels: &'a mut Vec<IndexedInstantiationRecord>,
    asserted_instantiations: &'a mut Vec<Term>,
    num_quantifiers_instantiated: &'a mut u64,
    assertion_tracker: &'a mut InstantiationAssertionTracker,
}

impl<'a> InstantiationContext<'a> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        instantiations: &'a mut Vec<StoredInstantiation>,
        bmc_builder: &'a mut BMCBuilder,
        definition_materializer: &'a mut DefinitionMaterializer,
        solver: &'a mut dyn YardbirdSolver,
        subterm_handler: &'a mut SubtermHandler,
        track_instantiations: bool,
        tracked_labels: &'a mut Vec<IndexedInstantiationRecord>,
        asserted_instantiations: &'a mut Vec<Term>,
        num_quantifiers_instantiated: &'a mut u64,
        assertion_tracker: &'a mut InstantiationAssertionTracker,
    ) -> Self {
        Self {
            instantiations,
            bmc_builder,
            definition_materializer,
            solver,
            subterm_handler,
            track_instantiations,
            tracked_labels,
            asserted_instantiations,
            num_quantifiers_instantiated,
            assertion_tracker,
        }
    }

    pub fn solver_backend(&self) -> crate::SolverBackend {
        self.solver.backend()
    }

    /// Monotonic identifier for the solver model currently available to a
    /// model-aware instantiation policy.
    pub fn solver_check_epoch(&self) -> u64 {
        self.solver
            .statistics_ref()
            .get_f64("num checks")
            .unwrap_or_default() as u64
    }

    /// Installs a newly selected instance at every currently eligible frame.
    ///
    /// Exact-frame placement is intentionally unavailable until provenance is
    /// carried by each selected candidate rather than inferred globally.
    pub fn install_new(&mut self, request: InstantiationRequest) -> InstantiationInstallResult {
        let Some(stored) = self.store_new(request) else {
            return InstantiationInstallResult::default();
        };
        self.assertion_tracker.record_all_eligible_frame_placement();

        let cur_depth = self.bmc_builder.depth;
        let mut result = InstantiationInstallResult {
            abstract_instance_added: true,
            ..InstantiationInstallResult::default()
        };

        let mut indexed_instances = Vec::new();
        for frame in (stored.inst.width()..=cur_depth).rev() {
            self.bmc_builder.set_depth(frame);
            self.bmc_builder.set_width(stored.inst.width());
            let rewritten = stored.inst.rewrite(self.bmc_builder);
            let substitution = stored
                .provenance
                .as_ref()
                .map(|provenance| provenance.at_frame(self.bmc_builder))
                .unwrap_or_default();
            let (indexed_instance, _) =
                self.materialize_indexed_instance(rewritten, true, &mut result);
            log::trace!(
                "[yardbird::inst-trace] placement=all-eligible-frames indexed-term={indexed_instance}"
            );
            result.indexed_assertions_attempted += 1;
            if !self
                .assertion_tracker
                .accept(&indexed_instance, AssertionKind::IndexedTheory)
            {
                result.indexed_assertions_deduplicated += 1;
                continue;
            }
            result.indexed_assertions_added += 1;
            self.asserted_instantiations.push(indexed_instance.clone());
            indexed_instances.push(PreparedIndexedInstantiation {
                term: indexed_instance,
                frame,
                substitution,
                provenance: stored.provenance.clone(),
            });
        }
        self.bmc_builder.set_depth(cur_depth);
        *self.num_quantifiers_instantiated += indexed_instances.len() as u64;

        self.assert_new_instances(&indexed_instances, cur_depth);
        result
    }

    /// Retains a new abstract theory instance without choosing its placements.
    pub fn store_new(&mut self, request: InstantiationRequest) -> Option<StoredInstantiation> {
        if self
            .instantiations
            .iter()
            .any(|stored| stored.inst == request.inst)
        {
            debug!("ALREADY SEEN {}!", request.inst);
            return None;
        }

        let stored = StoredInstantiation {
            inst: request.inst,
            provenance: request.provenance,
        };
        debug!("USED INSTANCE: {}", stored.inst);
        self.solver
            .register_quantified_variables(stored.inst.get_term())
            .expect("solver should register quantified variables");
        self.instantiations.push(stored.clone());
        self.assertion_tracker.record_abstract_instance();
        Some(stored)
    }

    /// Installs every unplaced stored schema that is false in the captured model.
    ///
    /// `covered_placements` is strategy-owned because deciding whether a true
    /// placement should be reconsidered in a later model is policy, not solver
    /// bookkeeping. Placements already asserted (or canonically deduplicated)
    /// are permanently covered; model-true placements remain eligible later.
    pub fn install_model_violated_schemas(
        &mut self,
        covered_placements: &mut HashSet<(String, u16)>,
    ) -> anyhow::Result<InstantiationInstallResult> {
        let stored_instances = self.instantiations.clone();
        self.assertion_tracker.record_schema_batch_pass();
        self.install_model_violated_schema_set(stored_instances, covered_placements)
    }

    /// Installs the violated placements of one newly retained schema.
    pub fn install_model_violated_schema(
        &mut self,
        stored: StoredInstantiation,
        covered_placements: &mut HashSet<(String, u16)>,
    ) -> anyhow::Result<InstantiationInstallResult> {
        self.install_model_violated_schema_set(vec![stored], covered_placements)
    }

    fn install_model_violated_schema_set(
        &mut self,
        stored_instances: Vec<StoredInstantiation>,
        covered_placements: &mut HashSet<(String, u16)>,
    ) -> anyhow::Result<InstantiationInstallResult> {
        let cur_depth = self.bmc_builder.depth;
        let mut result = InstantiationInstallResult::default();
        let mut indexed_instances = Vec::new();

        for stored in stored_instances {
            let schema_key = stored.inst.to_string();
            for frame in (stored.inst.width()..=cur_depth).rev() {
                let placement_key = (schema_key.clone(), frame);
                if covered_placements.contains(&placement_key) {
                    continue;
                }

                self.bmc_builder.set_depth(frame);
                self.bmc_builder.set_width(stored.inst.width());
                let rewritten = stored.inst.rewrite(self.bmc_builder);
                let substitution = stored
                    .provenance
                    .as_ref()
                    .map(|provenance| provenance.at_frame(self.bmc_builder))
                    .unwrap_or_default();
                let (indexed_instance, introduced_support) =
                    self.materialize_indexed_instance(rewritten, false, &mut result);

                let violated = if introduced_support {
                    // The captured model predates this helper definition, so
                    // its value is not meaningful there. Installing the valid
                    // theory instance eagerly is the conservative fallback.
                    self.assertion_tracker
                        .record_schema_placement_eager_fallback();
                    true
                } else {
                    self.assertion_tracker.record_schema_placement_evaluation();
                    match self.solver.eval_to_string(&indexed_instance)?.trim() {
                        "false" => true,
                        "true" => false,
                        value => anyhow::bail!(
                            "schema placement did not evaluate to Bool: {value} for {indexed_instance}"
                        ),
                    }
                };

                if !violated {
                    continue;
                }
                self.assertion_tracker.record_schema_placement_violation();
                result.indexed_assertions_attempted += 1;
                covered_placements.insert(placement_key);
                if !self
                    .assertion_tracker
                    .accept(&indexed_instance, AssertionKind::IndexedTheory)
                {
                    result.indexed_assertions_deduplicated += 1;
                    continue;
                }

                result.indexed_assertions_added += 1;
                self.asserted_instantiations.push(indexed_instance.clone());
                self.subterm_handler
                    .register_instantiation_term(indexed_instance.clone());
                indexed_instances.push(PreparedIndexedInstantiation {
                    term: indexed_instance,
                    frame,
                    substitution,
                    provenance: stored.provenance.clone(),
                });
            }
        }

        self.bmc_builder.set_depth(cur_depth);
        *self.num_quantifiers_instantiated += indexed_instances.len() as u64;
        self.assert_schema_batch(&indexed_instances, cur_depth);
        Ok(result)
    }

    /// Replays every stored instance at the BMC builder's current depth.
    pub fn install_existing_at_current_depth(&mut self, depth: u16) {
        let stored_instances = self.instantiations.clone();
        if stored_instances.is_empty() {
            return;
        }

        let mut indexed_instances = Vec::new();
        for stored in stored_instances {
            self.bmc_builder.set_width(stored.inst.width());
            let rewritten = stored.inst.rewrite(self.bmc_builder);
            let substitution = stored
                .provenance
                .as_ref()
                .map(|provenance| provenance.at_frame(self.bmc_builder))
                .unwrap_or_default();
            let mut ignored_result = InstantiationInstallResult::default();
            let (indexed_instance, _) =
                self.materialize_indexed_instance(rewritten, false, &mut ignored_result);
            if !self
                .assertion_tracker
                .accept(&indexed_instance, AssertionKind::IndexedTheory)
            {
                continue;
            }
            self.asserted_instantiations.push(indexed_instance.clone());
            indexed_instances.push(PreparedIndexedInstantiation {
                term: indexed_instance,
                frame: depth,
                substitution,
                provenance: stored.provenance,
            });
        }
        *self.num_quantifiers_instantiated += indexed_instances.len() as u64;

        if self.track_instantiations {
            for indexed_instance in indexed_instances {
                let inst_num = self.tracked_labels.len();
                let label = format!("inst_{inst_num}_depth_{depth}");
                self.solver
                    .assert_tracked_instantiation(&label, &indexed_instance.term)
                    .expect("solver should assert tracked instantiations");
                self.record_tracked_instance(
                    label,
                    &indexed_instance,
                    depth,
                    0,
                    indexed_instance.provenance.as_ref(),
                );
            }
        } else {
            let terms = indexed_instances
                .into_iter()
                .map(|indexed_instance| indexed_instance.term)
                .collect::<Vec<_>>();
            self.solver
                .assert_instantiation_batch(&terms)
                .expect("solver should assert instantiations");
        }
    }

    fn materialize_indexed_instance(
        &mut self,
        indexed_instance: Term,
        register_root_subterms: bool,
        result: &mut InstantiationInstallResult,
    ) -> (Term, bool) {
        let materialized = self
            .definition_materializer
            .materialize(indexed_instance, self.bmc_builder);
        let introduced_support =
            !materialized.new_declarations.is_empty() || !materialized.new_definitions.is_empty();
        for declaration in &materialized.new_declarations {
            self.solver
                .accept_command(declaration)
                .expect("solver should accept an instantiation helper declaration");
        }
        for definition in &materialized.new_definitions {
            result.helper_assertions_attempted += 1;
            if self
                .assertion_tracker
                .accept(definition, AssertionKind::HelperDefinition)
            {
                result.helper_assertions_added += 1;
                self.solver
                    .assert_term(definition)
                    .expect("solver should assert an instantiation helper definition");
            } else {
                result.helper_assertions_deduplicated += 1;
            }
        }
        if register_root_subterms {
            self.subterm_handler
                .register_instantiation_term(materialized.root.clone());
        }
        for support in materialized.support {
            self.subterm_handler.register_instantiation_term(support);
        }
        (materialized.root, introduced_support)
    }

    fn assert_new_instances(
        &mut self,
        indexed_instances: &[PreparedIndexedInstantiation],
        depth: u16,
    ) {
        if self.track_instantiations {
            for (unroll_index, indexed_instance) in indexed_instances.iter().enumerate() {
                let inst_num = self.tracked_labels.len();
                let label = format!("inst_{inst_num}_{unroll_index}");
                self.solver
                    .assert_tracked_instantiation(&label, &indexed_instance.term)
                    .expect("solver should assert tracked instantiations");
                self.record_tracked_instance(
                    label,
                    indexed_instance,
                    depth,
                    unroll_index as u16,
                    indexed_instance.provenance.as_ref(),
                );
            }
        } else {
            self.solver
                .assert_instantiation_batch(
                    &indexed_instances
                        .iter()
                        .map(|indexed| indexed.term.clone())
                        .collect::<Vec<_>>(),
                )
                .expect("solver should assert instantiations");
        }
    }

    fn assert_schema_batch(
        &mut self,
        indexed_instances: &[PreparedIndexedInstantiation],
        depth: u16,
    ) {
        if indexed_instances.is_empty() {
            return;
        }

        if self.track_instantiations {
            for (batch_index, indexed_instance) in indexed_instances.iter().enumerate() {
                let inst_num = self.tracked_labels.len();
                let label = format!("inst_{inst_num}_schema_batch_{depth}");
                self.solver
                    .assert_tracked_instantiation(&label, &indexed_instance.term)
                    .expect("solver should assert tracked schema-batch instantiations");
                self.record_tracked_instance(
                    label,
                    indexed_instance,
                    depth,
                    batch_index as u16,
                    indexed_instance.provenance.as_ref(),
                );
            }
        } else {
            self.solver
                .assert_instantiation_batch(
                    &indexed_instances
                        .iter()
                        .map(|indexed| indexed.term.clone())
                        .collect::<Vec<_>>(),
                )
                .expect("solver should assert schema-batch instantiations");
        }
    }

    fn record_tracked_instance(
        &mut self,
        label: String,
        indexed: &PreparedIndexedInstantiation,
        depth: u16,
        unroll_index: u16,
        provenance: Option<&InstantiationProvenance>,
    ) {
        let term = indexed.term.to_string();
        self.tracked_labels.push(IndexedInstantiationRecord {
            label,
            term_hash: crate::training::canonical_term_hash_from_string(&term),
            term,
            depth,
            frame: indexed.frame,
            unroll_index,
            substitution: indexed.substitution.clone(),
            abstract_instantiation_id: provenance
                .map(|provenance| provenance.abstract_instantiation_id().to_string()),
            in_unsat_core: false,
        });
    }
}

/// Policy controlling when stored quantifier instantiations are replayed.
pub trait InstantiationStrategy: std::fmt::Debug + Send {
    fn clone_box(&self) -> Box<dyn InstantiationStrategy>;

    fn on_generate(
        &mut self,
        request: InstantiationRequest,
        context: &mut InstantiationContext<'_>,
    ) -> InstantiationInstallResult {
        context.install_new(request)
    }

    fn on_loop(&mut self, depth: u16, context: &mut InstantiationContext<'_>);
}
