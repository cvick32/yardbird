use std::{
    collections::BTreeMap,
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

use serde::{Deserialize, Serialize};

use crate::{solver::SolverCheckResult, utils::SolverStatistics, SolverBackend};

static RUN_ID_SEQUENCE: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(default)]
pub struct ProfilingRunRecord {
    pub timing_secs: BTreeMap<String, f64>,
    pub driver_records: Vec<DriverProfilingRecord>,
    pub cost_records: Vec<ProfilingRecord>,
    pub solver_checks: Vec<SolverCheckProfilingRecord>,
}

#[derive(Debug, Clone)]
struct ProfilingMetadata {
    run_id: String,
    benchmark_id: String,
    strategy: String,
    cost_function: String,
    theory: String,
}

impl ProfilingMetadata {
    fn from_options(options: &crate::YardbirdOptions) -> Self {
        Self {
            run_id: next_run_id(),
            benchmark_id: options
                .filename
                .clone()
                .unwrap_or_else(|| "<unknown>".to_string()),
            strategy: options.strategy.to_string(),
            cost_function: options.cost_function.to_string(),
            theory: options.theory.to_string(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Profiler {
    metadata: ProfilingMetadata,
    profile: ProfilingRunRecord,
    previous_instance_count: u64,
}

impl Profiler {
    pub fn from_options(options: &crate::YardbirdOptions) -> Self {
        Self {
            metadata: ProfilingMetadata::from_options(options),
            profile: ProfilingRunRecord::default(),
            previous_instance_count: 0,
        }
    }

    pub(crate) fn record_solver_check(
        &mut self,
        context: SolverCheckContext,
        measurement: SolverCheckMeasurement,
    ) {
        let check_id = self.profile.solver_checks.len() as u64;
        let instances_added_since_previous_check = context
            .instances_total
            .saturating_sub(self.previous_instance_count);
        self.previous_instance_count = context.instances_total;

        self.profile.solver_checks.push(SolverCheckProfilingRecord {
            run_id: self.metadata.run_id.clone(),
            check_id,
            benchmark_id: self.metadata.benchmark_id.clone(),
            depth: context.depth,
            refinement_id: context.refinement_id,
            refinement_step: context.refinement_step,
            strategy: self.metadata.strategy.clone(),
            cost_function: self.metadata.cost_function.clone(),
            theory: self.metadata.theory.clone(),
            backend: context.solver.backend,
            result: measurement.result,
            reason_unknown: measurement.reason_unknown,
            logic: context.solver.logic,
            solver_parameters: context.solver.parameters,
            random_seeds: context.solver.random_seeds,
            assertion_count: measurement.assertion_count,
            instances_total: context.instances_total,
            instances_added_since_previous_check,
            timing_ns: measurement.timing_ns,
            statistics_before: measurement.statistics_before,
            statistics_after: measurement.statistics_after,
            statistics_delta: measurement.statistics_delta,
        });
    }

    pub fn add_driver_record(&mut self, record: DriverProfilingRecord) {
        self.profile.driver_records.push(record);
    }

    pub fn extend_cost_records(&mut self, records: Vec<ProfilingRecord>) {
        self.profile.cost_records.extend(records);
    }

    pub fn record_timing(&mut self, stage: &'static str, duration: Duration) {
        *self
            .profile
            .timing_secs
            .entry(stage.to_string())
            .or_insert(0.0) += duration.as_secs_f64();
    }

    pub fn finish(self) -> ProfilingRunRecord {
        self.profile
    }

    pub fn snapshot(&self) -> ProfilingRunRecord {
        self.profile.clone()
    }
}

fn next_run_id() -> String {
    let timestamp_nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_nanos())
        .unwrap_or_default();
    let sequence = RUN_ID_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    format!(
        "yardbird-{timestamp_nanos}-pid{}-{sequence}",
        std::process::id()
    )
}

#[derive(Debug, Clone)]
pub(crate) struct SolverCheckContext {
    pub depth: u16,
    pub refinement_id: u32,
    pub refinement_step: u32,
    pub instances_total: u64,
    pub solver: SolverProfileMetadata,
}

#[derive(Debug, Clone)]
pub(crate) struct SolverProfileMetadata {
    pub backend: SolverBackend,
    pub logic: String,
    pub parameters: BTreeMap<String, String>,
    pub random_seeds: BTreeMap<String, u64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SolverCheckProfilingRecord {
    pub run_id: String,
    pub check_id: u64,
    pub benchmark_id: String,
    pub depth: u16,
    pub refinement_id: u32,
    pub refinement_step: u32,
    pub strategy: String,
    pub cost_function: String,
    pub theory: String,
    pub backend: SolverBackend,
    pub result: SolverCheckResult,
    pub reason_unknown: Option<String>,
    pub logic: String,
    pub solver_parameters: BTreeMap<String, String>,
    pub random_seeds: BTreeMap<String, u64>,
    pub assertion_count: u64,
    pub instances_total: u64,
    pub instances_added_since_previous_check: u64,
    pub timing_ns: SolverCheckTiming,
    pub statistics_before: SolverStatistics,
    pub statistics_after: SolverStatistics,
    pub statistics_delta: SolverStatistics,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SolverCheckTiming {
    pub property_push: u64,
    pub raw_check: u64,
    pub model_acquisition: u64,
    pub proof_core_access: u64,
    pub property_pop: u64,
    pub statistics_collection: u64,
    pub total_check_handling: u64,
}

#[derive(Debug, Copy, Clone)]
pub(crate) enum SolverCheckPhase {
    PropertyPush,
    ModelAcquisition,
    ProofCoreAccess,
    PropertyPop,
    StatisticsCollection,
}

pub(crate) struct SolverCheckTimer {
    total_start: Option<Instant>,
    statistics_before: Option<SolverStatistics>,
    timing: SolverCheckTiming,
}

impl SolverCheckTimer {
    pub fn new(enabled: bool, statistics: impl FnOnce() -> SolverStatistics) -> Self {
        Self {
            total_start: enabled.then(Instant::now),
            statistics_before: enabled.then(statistics),
            timing: SolverCheckTiming::default(),
        }
    }

    pub fn measure<T>(&mut self, phase: SolverCheckPhase, operation: impl FnOnce() -> T) -> T {
        let Some(start) = self.total_start.as_ref().map(|_| Instant::now()) else {
            return operation();
        };
        let result = operation();
        let elapsed = duration_nanos(start.elapsed());
        match phase {
            SolverCheckPhase::PropertyPush => self.timing.property_push = elapsed,
            SolverCheckPhase::ModelAcquisition => self.timing.model_acquisition = elapsed,
            SolverCheckPhase::ProofCoreAccess => self.timing.proof_core_access = elapsed,
            SolverCheckPhase::PropertyPop => self.timing.property_pop = elapsed,
            SolverCheckPhase::StatisticsCollection => {
                self.timing.statistics_collection = elapsed;
            }
        }
        result
    }

    pub fn measure_raw<T>(&mut self, operation: impl FnOnce() -> T) -> (T, Duration) {
        let start = Instant::now();
        let result = operation();
        let elapsed = start.elapsed();
        if self.total_start.is_some() {
            self.timing.raw_check = duration_nanos(elapsed);
        }
        (result, elapsed)
    }

    pub fn finish(
        mut self,
        result: SolverCheckResult,
        reason_unknown: Option<String>,
        assertion_count: u64,
        statistics: impl FnOnce() -> SolverStatistics,
    ) -> Option<SolverCheckMeasurement> {
        let total_start = self.total_start?;
        let statistics_before = self.statistics_before?;
        let statistics_after = statistics();
        self.timing.total_check_handling = duration_nanos(total_start.elapsed());

        Some(SolverCheckMeasurement {
            result,
            reason_unknown,
            assertion_count,
            timing_ns: self.timing,
            statistics_delta: statistics_after.delta_snapshot_since(&statistics_before),
            statistics_before,
            statistics_after,
        })
    }
}

fn duration_nanos(duration: Duration) -> u64 {
    duration.as_nanos().try_into().unwrap_or(u64::MAX)
}

#[derive(Debug, Clone)]
pub(crate) struct SolverCheckMeasurement {
    pub result: SolverCheckResult,
    pub reason_unknown: Option<String>,
    pub assertion_count: u64,
    pub timing_ns: SolverCheckTiming,
    pub statistics_before: SolverStatistics,
    pub statistics_after: SolverStatistics,
    pub statistics_delta: SolverStatistics,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProfilingRecord {
    pub scope: String,
    pub bmc_depth: Option<u16>,
    pub refinement_step: Option<u32>,
    pub array_types: Vec<(String, String)>,
    pub timing_secs: BTreeMap<String, f64>,
    pub counters: BTreeMap<String, u64>,
    pub cost_rec: CostRecProfile,
    pub egraph: EGraphProfile,
    pub scheduler: SchedulerProfile,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DriverProfilingRecord {
    pub bmc_depth: u16,
    pub refinement_step: u32,
    pub action: String,
    pub timing_secs: BTreeMap<String, f64>,
    pub unique_instances_before: usize,
    pub unique_instances_after: usize,
    pub indexed_assertions_before: u64,
    pub indexed_assertions_after: u64,
}

impl DriverProfilingRecord {
    pub fn new(
        bmc_depth: u16,
        refinement_step: u32,
        unique_instances_before: usize,
        indexed_assertions_before: u64,
    ) -> Self {
        Self {
            bmc_depth,
            refinement_step,
            action: String::new(),
            timing_secs: BTreeMap::new(),
            unique_instances_before,
            unique_instances_after: unique_instances_before,
            indexed_assertions_before,
            indexed_assertions_after: indexed_assertions_before,
        }
    }

    pub fn record_timing(&mut self, stage: &'static str, duration: Duration) {
        *self.timing_secs.entry(stage.to_string()).or_insert(0.0) += duration.as_secs_f64();
    }

    pub fn record_timing_secs(&mut self, stage: impl Into<String>, secs: f64) {
        *self.timing_secs.entry(stage.into()).or_insert(0.0) += secs;
    }

    pub fn finish(
        mut self,
        action: impl Into<String>,
        unique_instances_after: usize,
        indexed_assertions_after: u64,
    ) -> Self {
        self.action = action.into();
        self.unique_instances_after = unique_instances_after;
        self.indexed_assertions_after = indexed_assertions_after;
        self
    }
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CostRecProfile {
    pub total_calls: u64,
    pub total_secs: f64,
    pub total_expr_nodes: u64,
    pub max_expr_nodes: usize,
    pub by_site: BTreeMap<String, CostRecSiteProfile>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CostRecSiteProfile {
    pub calls: u64,
    pub secs: f64,
    pub expr_nodes: u64,
    pub max_expr_nodes: usize,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct EGraphProfile {
    pub classes_before_update: Option<usize>,
    pub nodes_before_update: Option<usize>,
    pub classes_after_update: Option<usize>,
    pub nodes_after_update: Option<usize>,
    pub classes_before_saturation: Option<usize>,
    pub nodes_before_saturation: Option<usize>,
    pub classes_after_saturation: Option<usize>,
    pub nodes_after_saturation: Option<usize>,
    pub runner_iterations: Option<usize>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SchedulerProfile {
    pub search_rewrite_calls: u64,
    pub apply_rewrite_calls: u64,
    pub skipped_apply_calls: u64,
    pub matches_total: u64,
    pub substitutions_total: u64,
    pub substitutions_explored: u64,
    pub conflicts_total: u64,
    pub regular_instantiations: u64,
    pub const_or_high_cost_instantiations: u64,
    pub by_rewrite: BTreeMap<String, RewriteSchedulerProfile>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct RewriteSchedulerProfile {
    pub search_calls: u64,
    pub search_secs: f64,
    pub apply_calls: u64,
    pub apply_secs: f64,
    pub skipped_apply_calls: u64,
    pub matches_total: u64,
    pub substitutions_total: u64,
    pub substitutions_explored: u64,
    pub conflicts_total: u64,
    pub regular_instantiations: u64,
    pub const_or_high_cost_instantiations: u64,
}

pub struct ArrayProfilingCollector {
    record: ProfilingRecord,
}

impl ArrayProfilingCollector {
    pub fn new(
        scope: impl Into<String>,
        bmc_depth: Option<u16>,
        refinement_step: Option<u32>,
        array_types: Vec<(String, String)>,
    ) -> Self {
        Self {
            record: ProfilingRecord {
                scope: scope.into(),
                bmc_depth,
                refinement_step,
                array_types,
                timing_secs: BTreeMap::new(),
                counters: BTreeMap::new(),
                cost_rec: CostRecProfile::default(),
                egraph: EGraphProfile::default(),
                scheduler: SchedulerProfile::default(),
            },
        }
    }

    pub fn record_timing(&mut self, stage: &'static str, duration: Duration) {
        *self
            .record
            .timing_secs
            .entry(stage.to_string())
            .or_insert(0.0) += duration.as_secs_f64();
    }

    pub fn add_counter(&mut self, counter: &'static str, amount: u64) {
        *self.record.counters.entry(counter.to_string()).or_insert(0) += amount;
    }

    pub fn set_egraph_before_update(&mut self, classes: usize, nodes: usize) {
        self.record.egraph.classes_before_update = Some(classes);
        self.record.egraph.nodes_before_update = Some(nodes);
    }

    pub fn set_egraph_after_update(&mut self, classes: usize, nodes: usize) {
        self.record.egraph.classes_after_update = Some(classes);
        self.record.egraph.nodes_after_update = Some(nodes);
    }

    pub fn set_egraph_before_saturation(&mut self, classes: usize, nodes: usize) {
        self.record.egraph.classes_before_saturation = Some(classes);
        self.record.egraph.nodes_before_saturation = Some(nodes);
    }

    pub fn set_egraph_after_saturation(
        &mut self,
        classes: usize,
        nodes: usize,
        runner_iterations: usize,
    ) {
        self.record.egraph.classes_after_saturation = Some(classes);
        self.record.egraph.nodes_after_saturation = Some(nodes);
        self.record.egraph.runner_iterations = Some(runner_iterations);
    }

    pub fn record_cost<T>(
        &mut self,
        site: &'static str,
        expr_nodes: usize,
        compute: impl FnOnce() -> T,
    ) -> T {
        let start = Instant::now();
        let result = compute();
        let elapsed = start.elapsed();
        self.add_cost_record(site, expr_nodes, elapsed);
        result
    }

    pub fn record_search_rewrite(
        &mut self,
        rewrite_name: &str,
        matches: usize,
        substitutions: usize,
        duration: Duration,
    ) {
        let scheduler = &mut self.record.scheduler;
        scheduler.search_rewrite_calls += 1;
        scheduler.matches_total += matches as u64;
        scheduler.substitutions_total += substitutions as u64;

        let by_rewrite = scheduler
            .by_rewrite
            .entry(rewrite_name.to_string())
            .or_default();
        by_rewrite.search_calls += 1;
        by_rewrite.search_secs += duration.as_secs_f64();
        by_rewrite.matches_total += matches as u64;
        by_rewrite.substitutions_total += substitutions as u64;
    }

    pub fn record_apply_rewrite(
        &mut self,
        rewrite_name: &str,
        substitutions_explored: usize,
        skipped: bool,
        duration: Duration,
    ) {
        let scheduler = &mut self.record.scheduler;
        scheduler.apply_rewrite_calls += 1;
        scheduler.substitutions_explored += substitutions_explored as u64;
        if skipped {
            scheduler.skipped_apply_calls += 1;
        }

        let by_rewrite = scheduler
            .by_rewrite
            .entry(rewrite_name.to_string())
            .or_default();
        by_rewrite.apply_calls += 1;
        by_rewrite.apply_secs += duration.as_secs_f64();
        by_rewrite.substitutions_explored += substitutions_explored as u64;
        if skipped {
            by_rewrite.skipped_apply_calls += 1;
        }
    }

    pub fn record_conflict(&mut self, rewrite_name: &str, const_or_high_cost: bool) {
        let scheduler = &mut self.record.scheduler;
        scheduler.conflicts_total += 1;
        if const_or_high_cost {
            scheduler.const_or_high_cost_instantiations += 1;
        } else {
            scheduler.regular_instantiations += 1;
        }

        let by_rewrite = scheduler
            .by_rewrite
            .entry(rewrite_name.to_string())
            .or_default();
        by_rewrite.conflicts_total += 1;
        if const_or_high_cost {
            by_rewrite.const_or_high_cost_instantiations += 1;
        } else {
            by_rewrite.regular_instantiations += 1;
        }
    }

    pub fn finish(self) -> ProfilingRecord {
        self.record
    }

    fn add_cost_record(&mut self, site: &'static str, expr_nodes: usize, duration: Duration) {
        let secs = duration.as_secs_f64();
        self.record.cost_rec.total_calls += 1;
        self.record.cost_rec.total_secs += secs;
        self.record.cost_rec.total_expr_nodes += expr_nodes as u64;
        self.record.cost_rec.max_expr_nodes = self.record.cost_rec.max_expr_nodes.max(expr_nodes);

        let site_record = self
            .record
            .cost_rec
            .by_site
            .entry(site.to_string())
            .or_default();
        site_record.calls += 1;
        site_record.secs += secs;
        site_record.expr_nodes += expr_nodes as u64;
        site_record.max_expr_nodes = site_record.max_expr_nodes.max(expr_nodes);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::StatisticsValue;

    fn measurement(result: SolverCheckResult) -> SolverCheckMeasurement {
        let mut statistics_after = SolverStatistics::new();
        statistics_after.insert("conflicts".to_string(), StatisticsValue::UInt(3));
        let statistics_before = SolverStatistics::new();
        let statistics_delta = statistics_after.delta_snapshot_since(&statistics_before);

        SolverCheckMeasurement {
            result,
            reason_unknown: None,
            assertion_count: 2,
            timing_ns: SolverCheckTiming {
                raw_check: 25,
                total_check_handling: 40,
                ..SolverCheckTiming::default()
            },
            statistics_before,
            statistics_after,
            statistics_delta,
        }
    }

    fn context(refinement_step: u32, instances_total: u64) -> SolverCheckContext {
        SolverCheckContext {
            depth: 0,
            refinement_id: refinement_step + 1,
            refinement_step,
            instances_total,
            solver: SolverProfileMetadata {
                backend: SolverBackend::Z3,
                logic: "QF_AUFLIA".to_string(),
                parameters: BTreeMap::from([("random_seed".to_string(), "0".to_string())]),
                random_seeds: BTreeMap::from([("random_seed".to_string(), 0)]),
            },
        }
    }

    #[test]
    fn profiler_owns_check_identity_instance_deltas_and_serialization() {
        let mut options =
            crate::YardbirdOptions::from_filename("examples/array/array_copy.vmt".to_string());
        options.strategy = crate::Strategy::Concrete;
        options.profile = true;
        let mut profiler = Profiler::from_options(&options);

        profiler.record_solver_check(context(0, 2), measurement(SolverCheckResult::Sat));
        profiler.record_solver_check(context(1, 5), measurement(SolverCheckResult::Unsat));

        let serialized = serde_json::to_string(&profiler.finish()).unwrap();
        let json: serde_json::Value = serde_json::from_str(&serialized).unwrap();
        let profile: ProfilingRunRecord = serde_json::from_str(&serialized).unwrap();

        assert!(json.get("schema_version").is_none());
        assert!(json.get("enabled").is_none());
        assert!(json.get("solver_profiling_enabled").is_none());
        assert!(json.get("cost_profiling_enabled").is_none());
        assert!(json["solver_checks"][0]
            .get("transcript_prefix_sha256")
            .is_none());
        assert!(json["solver_checks"][0].get("transcript_path").is_none());
        assert_eq!(profile.solver_checks.len(), 2);
        assert_eq!(profile.solver_checks[0].check_id, 0);
        assert_eq!(profile.solver_checks[1].check_id, 1);
        assert_eq!(
            profile.solver_checks[0].run_id,
            profile.solver_checks[1].run_id
        );
        assert_eq!(
            profile.solver_checks[0].instances_added_since_previous_check,
            2
        );
        assert_eq!(
            profile.solver_checks[1].instances_added_since_previous_check,
            3
        );
        assert_eq!(
            profile.solver_checks[1]
                .statistics_delta
                .get_f64("conflicts"),
            Some(3.0)
        );
    }
}
