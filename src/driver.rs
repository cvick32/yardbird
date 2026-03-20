use itertools::Itertools;
use log::info;
use serde::{ser::SerializeStruct, Deserialize, Serialize};
use smt2parser::{concrete::Term, get_term_from_term_string, vmt::VMTModel};

use crate::{
    instantiation_strategy::InstantiationStrategy,
    problem::Problem,
    strategies::{ProofAction, ProofStrategy, ProofStrategyExt},
    utils::SolverStatistics,
};

/// Information about the unsat core when tracking is enabled
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct UnsatCoreInfo {
    pub core_size: usize,
    pub core_instantiations: Vec<CoreInstantiation>,
}

/// A single instantiation in the unsat core
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CoreInstantiation {
    pub label: String,
    pub term: String,
}

#[derive(Debug, Default)]
pub struct ProofLoopResult {
    pub model: Option<VMTModel>,
    pub used_instances: Vec<Term>,
    pub const_instances: Vec<Term>,
    pub solver_statistics: SolverStatistics,
    pub total_instantiations_added: u64,
    pub total_refinement_steps: u32,
    pub counterexample: bool,
    pub found_proof: bool,
    pub unsat_core: Option<UnsatCoreInfo>,
    pub decision_data: Vec<crate::training::DecisionRecord>,
    pub abstract_instantiations: Vec<crate::training::AbstractInstantiationRecord>,
    pub indexed_instantiations: Vec<crate::training::IndexedInstantiationRecord>,
}

impl ProofLoopResult {
    pub fn get_instantiations_string(&self) -> String {
        self.used_instances
            .iter()
            .map(|inst| format!(" - {inst}"))
            .join("\n")
    }
}

impl Serialize for ProofLoopResult {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("ProofLoopResult", 11)?;
        state.serialize_field(
            "used_instances",
            &self
                .used_instances
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
        )?;
        state.serialize_field(
            "const_instances",
            &self
                .const_instances
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
        )?;
        state.serialize_field("solver_statistics", &self.solver_statistics)?;
        state.serialize_field(
            "total_instantiations_added",
            &self.total_instantiations_added,
        )?;
        state.serialize_field("total_refinement_steps", &self.total_refinement_steps)?;
        state.serialize_field("counterexample", &self.counterexample)?;
        state.serialize_field("found_proof", &self.found_proof)?;
        state.serialize_field("unsat_core", &self.unsat_core)?;
        state.serialize_field("decision_data", &self.decision_data)?;
        state.serialize_field("abstract_instantiations", &self.abstract_instantiations)?;
        state.serialize_field("indexed_instantiations", &self.indexed_instantiations)?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for ProofLoopResult {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::{MapAccess, Visitor};

        #[derive(Deserialize)]
        #[serde(field_identifier, rename_all = "snake_case")]
        enum Field {
            UsedInstances,
            ConstInstances,
            SolverStatistics,
            TotalInstantiationsAdded,
            TotalRefinementSteps,
            Counterexample,
            FoundProof,
            UnsatCore,
            DecisionData,
            AbstractInstantiations,
            IndexedInstantiations,
        }

        struct ProofLoopResultVisitor;

        impl<'de> Visitor<'de> for ProofLoopResultVisitor {
            type Value = ProofLoopResult;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("struct ProofLoopResult")
            }

            fn visit_map<V>(self, mut map: V) -> std::result::Result<ProofLoopResult, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut used_instances: Option<Vec<String>> = None;
                let mut const_instances: Option<Vec<String>> = None;
                let mut solver_statistics = None;
                let mut total_instantiations_added = None;
                let mut total_refinement_steps = None;
                let mut counterexample = None;
                let mut found_proof = None;
                let mut unsat_core = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::UsedInstances => {
                            used_instances = Some(map.next_value()?);
                        }
                        Field::ConstInstances => {
                            const_instances = Some(map.next_value()?);
                        }
                        Field::SolverStatistics => {
                            solver_statistics = Some(map.next_value()?);
                        }
                        Field::TotalInstantiationsAdded => {
                            total_instantiations_added = Some(map.next_value()?);
                        }
                        Field::TotalRefinementSteps => {
                            total_refinement_steps = Some(map.next_value()?);
                        }
                        Field::Counterexample => {
                            counterexample = Some(map.next_value()?);
                        }
                        Field::FoundProof => {
                            found_proof = Some(map.next_value()?);
                        }
                        Field::UnsatCore => {
                            unsat_core = Some(map.next_value()?);
                        }
                        Field::DecisionData
                        | Field::AbstractInstantiations
                        | Field::IndexedInstantiations => {
                            let _: serde::de::IgnoredAny = map.next_value()?;
                        }
                    }
                }

                // Parse term strings back into Term objects
                let used_instances_terms = used_instances
                    .unwrap_or_default()
                    .into_iter()
                    .map(|s| get_term_from_term_string(&s))
                    .collect();

                let const_instances_terms = const_instances
                    .unwrap_or_default()
                    .into_iter()
                    .map(|s| get_term_from_term_string(&s))
                    .collect();

                Ok(ProofLoopResult {
                    model: None,
                    used_instances: used_instances_terms,
                    const_instances: const_instances_terms,
                    solver_statistics: solver_statistics
                        .ok_or_else(|| serde::de::Error::missing_field("solver_statistics"))?,
                    total_instantiations_added: total_instantiations_added.ok_or_else(|| {
                        serde::de::Error::missing_field("total_instantiations_added")
                    })?,
                    total_refinement_steps: total_refinement_steps
                        .ok_or_else(|| serde::de::Error::missing_field("total_refinement_steps"))?,
                    counterexample: counterexample
                        .ok_or_else(|| serde::de::Error::missing_field("counterexample"))?,
                    found_proof: found_proof
                        .ok_or_else(|| serde::de::Error::missing_field("found_proof"))?,
                    unsat_core: unsat_core.flatten(),
                    decision_data: vec![],
                    abstract_instantiations: vec![],
                    indexed_instantiations: vec![],
                })
            }
        }

        const FIELDS: &[&str] = &[
            "used_instances",
            "const_instances",
            "solver_statistics",
            "total_instantiations_added",
            "total_refinement_steps",
            "counterexample",
            "found_proof",
            "unsat_core",
        ];
        deserializer.deserialize_struct("ProofLoopResult", FIELDS, ProofLoopResultVisitor)
    }
}

#[derive(Debug)]
pub struct Driver<'ctx, S> {
    pub used_instances: Vec<Term>,
    pub const_instances: Vec<Term>,
    pub vmt_model: VMTModel,
    extensions: DriverExtensions<'ctx, S>,
    dump_solver_path: Option<String>,
    track_instantiations: bool,
    dump_unsat_core_path: Option<String>,
    instantiation_strategy: Box<dyn InstantiationStrategy>,
}

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Found counter-example")]
    Counterexample,

    #[error(
        "No progress at depth {depth}\nUsed Instantiations:\n{insts}",
        insts = instantiations
            .iter()
            .map(|inst| format!(" - {inst}"))
            .join("\n")
    )]
    NoProgress {
        depth: u16,
        instantiations: Vec<Term>,
    },

    #[error("Hit refinement limit of {n_refines} at depth {depth}")]
    TooManyRefinements { n_refines: u32, depth: u16 },

    #[error("Error: {0}")]
    Anyhow(#[from] anyhow::Error),

    #[error("Solver returned unknown: {0:?}")]
    SolverUnknown(Option<String>),

    #[error("Unable to parse into e-graph: {0}")]
    RecExpr(#[from] egg::RecExprParseError<egg::FromOpError>),
}

pub type Result<T> = std::result::Result<T, Error>;

impl<'ctx, S> Driver<'ctx, S> {
    pub fn new(
        vmt_model: VMTModel,
        instantiation_strategy: Box<dyn InstantiationStrategy>,
    ) -> Self {
        Self {
            used_instances: vec![],
            const_instances: vec![],
            vmt_model,
            extensions: DriverExtensions::default(),
            dump_solver_path: None,
            track_instantiations: false,
            dump_unsat_core_path: None,
            instantiation_strategy,
        }
    }

    pub fn with_tracking_options(
        mut self,
        dump_solver: Option<String>,
        track_instantiations: bool,
        dump_unsat_core: Option<String>,
    ) -> Self {
        self.dump_solver_path = dump_solver;
        self.track_instantiations = track_instantiations;
        self.dump_unsat_core_path = dump_unsat_core;
        self
    }

    pub fn add_extension(&mut self, ext: impl ProofStrategyExt<S> + 'ctx) -> &mut Self {
        self.extensions.add_extension(ext);
        self
    }

    /// The main control flow of the proof loop.
    ///
    /// We loop up until the `target_depth`. For each of these BMC loops, we loop up to
    /// `n_refines` times. Each time, we unroll the `vmt_model` up to the current depth,
    /// ask the solver if we have any counter-examples this loop, and then continue.
    ///
    /// The `ProofStrategy` specified by `stat` defines what we do in the case of the
    /// model returning `Unsat`, `Unknown`, and `Sat`.
    pub fn check_strategy(
        &mut self,
        target_depth: u16,
        mut strat: Box<dyn ProofStrategy<'ctx, S>>,
    ) -> Result<ProofLoopResult> {
        self.vmt_model = strat.configure_model(self.vmt_model.clone());
        let n_refines = strat.n_refines();
        let mut total_refinement_steps = 0;

        let mut smt_problem = crate::smt_problem::SMTProblem::new(
            &self.vmt_model,
            &strat,
            self.track_instantiations,
            self.instantiation_strategy.clone_box(),
        );

        'bmc: for depth in 0..target_depth {
            info!("STARTING BMC FOR DEPTH {depth}");
            for refinement_step in 0..n_refines {
                info!("  refining loop: {}/{n_refines}", refinement_step + 1);
                total_refinement_steps += 1;
                smt_problem.unroll(depth);
                let mut state = strat.setup(&smt_problem, depth)?;
                let action = match smt_problem.check() {
                    z3::SatResult::Unsat => {
                        // Handle solver dumping if requested
                        if let Some(ref path) = self.dump_solver_path {
                            info!("Dumping solver to: {}", path);
                            smt_problem.dump_solver_to_file(path)?;
                        }

                        // Handle unsat core dumping if requested
                        if let Some(ref path) = self.dump_unsat_core_path {
                            if self.track_instantiations {
                                info!("Dumping unsat core to: {}", path);
                                smt_problem.export_unsat_core_json(path)?;
                            } else {
                                log::warn!("--dump-unsat-core specified but --track-instantiations not enabled");
                            }
                        }

                        self.extensions.unsat(&mut state, &smt_problem)?;
                        strat.unsat(&mut state, &smt_problem)?
                    }
                    z3::SatResult::Unknown => {
                        self.extensions.unknown(&mut state, &smt_problem)?;
                        strat.unknown(&mut state, &smt_problem)?
                    }
                    z3::SatResult::Sat => {
                        self.extensions
                            .sat(&mut state, &smt_problem, refinement_step)?;
                        strat.sat(&mut state, &smt_problem, refinement_step)?
                    }
                };

                match action {
                    ProofAction::Continue => {
                        self.extensions.finish(&mut self.vmt_model, &mut state)?;
                        strat.finish(state, &mut smt_problem)?;
                    }
                    ProofAction::NextDepth => continue 'bmc,
                    ProofAction::FoundCounterexample => return Err(Error::Counterexample),
                    ProofAction::FoundProof => {
                        info!("Building final proof result");
                        let mut result = strat.result(&mut self.vmt_model.clone(), &smt_problem);
                        result.total_refinement_steps = total_refinement_steps;
                        info!("Collecting unsat core metadata");
                        result.unsat_core = self.build_unsat_core_info(&smt_problem);
                        info!("Collecting indexed instantiation records");
                        result.indexed_instantiations =
                            self.build_indexed_instantiation_records(&smt_problem);
                        self.annotate_instantiation_core_membership(&mut result);
                        info!("Final proof result is ready");
                        return Ok(result);
                    }
                }
            }
            return Err(Error::TooManyRefinements { n_refines, depth });
        }

        info!("Building final proof result");
        let mut result = strat.result(&mut self.vmt_model.clone(), &smt_problem);
        result.total_refinement_steps = total_refinement_steps;
        info!("Collecting unsat core metadata");
        result.unsat_core = self.build_unsat_core_info(&smt_problem);
        info!("Collecting indexed instantiation records");
        result.indexed_instantiations = self.build_indexed_instantiation_records(&smt_problem);
        self.annotate_instantiation_core_membership(&mut result);
        info!("Final proof result is ready");
        Ok(result)
    }

    /// Build UnsatCoreInfo from the SMT problem if tracking is enabled
    fn build_unsat_core_info(
        &self,
        smt_problem: &crate::smt_problem::SMTProblem,
    ) -> Option<UnsatCoreInfo> {
        if !self.track_instantiations {
            return None;
        }

        smt_problem.get_unsat_core().map(|core_labels| {
            use std::collections::HashSet;
            let core_set: HashSet<_> = core_labels.iter().collect();
            let core_instantiations = smt_problem
                .get_tracked_labels()
                .iter()
                .filter(|record| core_set.contains(&record.label))
                .map(|record| CoreInstantiation {
                    label: record.label.clone(),
                    term: record.term.clone(),
                })
                .collect::<Vec<_>>();
            UnsatCoreInfo {
                core_size: core_instantiations.len(),
                core_instantiations,
            }
        })
    }

    /// Build indexed instantiation records from the SMT problem's tracked labels.
    /// Each record represents a single indexed instantiation added to the solver.
    fn build_indexed_instantiation_records(
        &self,
        smt_problem: &crate::smt_problem::SMTProblem,
    ) -> Vec<crate::training::IndexedInstantiationRecord> {
        if !self.track_instantiations {
            return vec![];
        }

        let core_set: std::collections::HashSet<String> = smt_problem
            .get_unsat_core()
            .unwrap_or_default()
            .into_iter()
            .collect();

        smt_problem
            .get_tracked_labels()
            .iter()
            .cloned()
            .map(|record| crate::training::IndexedInstantiationRecord {
                in_unsat_core: core_set.contains(&record.label),
                ..record
            })
            .collect()
    }

    fn annotate_instantiation_core_membership(&self, result: &mut ProofLoopResult) {
        let core_ids: std::collections::HashSet<String> = result
            .indexed_instantiations
            .iter()
            .filter(|record| record.in_unsat_core)
            .filter_map(|record| record.abstract_instantiation_id.clone())
            .collect();
        for instantiation in &mut result.abstract_instantiations {
            instantiation.in_unsat_core =
                core_ids.contains(&instantiation.abstract_instantiation_id);
        }
    }
}

struct DriverExtensions<'ctx, S> {
    extensions: Vec<Box<dyn ProofStrategyExt<S> + 'ctx>>,
}

impl<S> std::fmt::Debug for DriverExtensions<'_, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("[<exts..>]")
    }
}

impl<S> Default for DriverExtensions<'_, S> {
    fn default() -> Self {
        Self { extensions: vec![] }
    }
}

impl<'ctx, S> DriverExtensions<'ctx, S> {
    pub fn add_extension(&mut self, ext: impl ProofStrategyExt<S> + 'ctx) -> &mut Self {
        self.extensions.push(Box::new(ext));
        self
    }
}

impl<S> ProofStrategyExt<S> for DriverExtensions<'_, S> {
    fn unsat(
        &mut self,
        state: &mut S,
        smt: &dyn crate::solver_interface::SolverInterface,
    ) -> anyhow::Result<()> {
        for ext in &mut self.extensions {
            ext.unsat(state, smt)?;
        }

        Ok(())
    }

    fn sat(
        &mut self,
        state: &mut S,
        smt: &dyn crate::solver_interface::SolverInterface,
        refinement_step: u32,
    ) -> anyhow::Result<()> {
        for ext in &mut self.extensions {
            ext.sat(state, smt, refinement_step)?;
        }

        Ok(())
    }

    fn unknown(
        &mut self,
        state: &mut S,
        smt: &dyn crate::solver_interface::SolverInterface,
    ) -> anyhow::Result<()> {
        for ext in &mut self.extensions {
            ext.unknown(state, smt)?;
        }
        Ok(())
    }

    fn finish(&mut self, model: &mut VMTModel, state: &mut S) -> anyhow::Result<()> {
        for ext in &mut self.extensions {
            ext.finish(model, state)?;
        }
        Ok(())
    }
}
