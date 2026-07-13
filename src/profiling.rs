use std::{
    collections::BTreeMap,
    time::{Duration, Instant},
};

use serde::{Deserialize, Serialize};

pub const PROFILING_SCHEMA_VERSION: &str = "yardbird-profile-v1";

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProfilingRunRecord {
    pub schema_version: String,
    pub enabled: bool,
    pub timing_secs: BTreeMap<String, f64>,
    pub driver_records: Vec<DriverProfilingRecord>,
    pub records: Vec<ProfilingRecord>,
}

impl ProfilingRunRecord {
    pub fn disabled() -> Self {
        Self {
            schema_version: PROFILING_SCHEMA_VERSION.to_string(),
            enabled: false,
            timing_secs: BTreeMap::new(),
            driver_records: vec![],
            records: vec![],
        }
    }

    pub fn enabled(records: Vec<ProfilingRecord>) -> Self {
        Self {
            schema_version: PROFILING_SCHEMA_VERSION.to_string(),
            enabled: true,
            timing_secs: BTreeMap::new(),
            driver_records: vec![],
            records,
        }
    }

    pub fn record_timing(&mut self, stage: &'static str, duration: Duration) {
        *self.timing_secs.entry(stage.to_string()).or_insert(0.0) += duration.as_secs_f64();
    }

    pub fn extend_driver_records(&mut self, records: Vec<DriverProfilingRecord>) {
        self.driver_records.extend(records);
    }
}

impl Default for ProfilingRunRecord {
    fn default() -> Self {
        Self::disabled()
    }
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
