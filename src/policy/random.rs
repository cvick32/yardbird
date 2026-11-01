//! Seeded uninformed proposals over the same catalogue as the API policies.
//! Sampling never consults model values, costs, relevance, or validation feedback.
//! Only the shared validator decides whether a complete instance can be installed.

use std::{
    collections::BTreeMap,
    fs::{File, OpenOptions},
    io::Write,
    path::PathBuf,
    time::Instant,
};

use rand::{rngs::StdRng, Rng, SeedableRng};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

use crate::{
    instance_installation::full_unroll::FullUnrollStrategy,
    policy::{
        discovery::{DiscoveryContext, DiscoveryFirst, InstanceDiscovery},
        instance_selection::TermCostInstantiationRanker,
        instantiation::{
            validate, InstantiationProposal, InstantiationSession, InstantiationSnapshot,
        },
        term_selection::array::ArrayBMCCost,
        NamedPolicy, YardbirdPolicy,
    },
    rule_matching::candidate::SymbolicInstance,
    solver::PropertyCheckMode,
    strategies::Abstract,
    theories::array::instantiation_schema::ArrayInstantiationSchema,
    ArrayProofPlan, SolverBackend, Theory, TheorySelection, YardbirdOptions,
};

const DISTRIBUTION: &str = "uniform_axiom_then_independent_slots_with_replacement_v1";

#[derive(clap::Args, Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(default)]
pub struct RandomOptions {
    /// PRNG seed; reproducible for a fixed build, catalogue order, and solver trajectory.
    #[arg(long, default_value_t = 0)]
    pub random_seed: u64,
    /// Maximum complete random proposals per countermodel; stop at the first accepted one.
    #[arg(long, default_value_t = 1)]
    pub random_samples: usize,
    /// New JSONL file for snapshots, proposals, validation outcomes, and episode totals.
    #[arg(long)]
    pub random_log: Option<PathBuf>,
}

impl Default for RandomOptions {
    fn default() -> Self {
        Self {
            random_seed: 0,
            random_samples: 1,
            random_log: None,
        }
    }
}

impl RandomOptions {
    pub fn validate(&self, run: &YardbirdOptions) -> anyhow::Result<()> {
        if run.policy != Some(NamedPolicy::RandomInstantiation) {
            anyhow::ensure!(
                self == &Self::default(),
                "--random-* options require --policy random-instantiation"
            );
            return Ok(());
        }
        anyhow::ensure!(
            run.filename.as_deref().is_some_and(|f| f.ends_with(".vmt")),
            "random instantiation requires a VMT input"
        );
        anyhow::ensure!(
            run.solver == SolverBackend::Z3
                && (run.theory == TheorySelection::Auto
                    || run.theory == TheorySelection::Explicit(vec![Theory::Array])),
            "random instantiation requires Z3 and --theory auto or array"
        );
        anyhow::ensure!(!run.eager && run.countermodel_trace_work == 0 &&
            run.synthesis_trigger == crate::SynthesisTrigger::Off && !run.prefer_axioms,
            "random instantiation does not support eager seeding, countermodel tracing, auxiliary synthesis, or prefer-axioms");
        anyhow::ensure!(self.random_samples > 0, "--random-samples must be positive");
        let log = self.random_log.as_ref().ok_or_else(|| {
            anyhow::anyhow!("random instantiation requires --random-log <NEW_JSONL_FILE>")
        })?;
        anyhow::ensure!(
            !log.exists(),
            "random log already exists: {}; choose a new path",
            log.display()
        );
        Ok(())
    }
}

/// Uniform over eligible axioms, then independently uniform over each slot's
/// full syntactic sort domain. This is not uniform over the union of all tuples:
/// axioms with more slots do not receive more probability mass.
struct ProposalSampler<'a> {
    schemas: Vec<&'a ArrayInstantiationSchema>,
    domains: BTreeMap<&'a str, Vec<&'a str>>,
}

impl<'a> ProposalSampler<'a> {
    fn new(snapshot: &'a InstantiationSnapshot) -> Self {
        let mut domains: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for term in &snapshot.terms {
            domains.entry(&term.sort).or_default().push(&term.id);
        }
        let schemas = snapshot
            .schemas
            .iter()
            .filter(|schema| {
                schema
                    .slots
                    .values()
                    .all(|sort| domains.contains_key(sort.as_str()))
            })
            .collect();
        Self { schemas, domains }
    }

    fn sample(&self, rng: &mut impl Rng) -> Option<InstantiationProposal> {
        if self.schemas.is_empty() {
            return None;
        }
        let schema = self.schemas[rng.random_range(0..self.schemas.len())];
        let bindings = schema
            .slots
            .iter()
            .map(|(slot, sort)| {
                let terms = &self.domains[sort.as_str()];
                (
                    slot.clone(),
                    terms[rng.random_range(0..terms.len())].to_owned(),
                )
            })
            .collect();
        Some(InstantiationProposal {
            axiom_id: schema.id.clone(),
            bindings,
        })
    }
}

pub(crate) fn build_plan(run: &YardbirdOptions) -> ArrayProofPlan {
    let policy = YardbirdPolicy::<ArrayBMCCost>::new(())
        .with_instantiation_ranker(Box::new(TermCostInstantiationRanker))
        .with_effort(DiscoveryFirst::default().with_no_fallback(run.no_guided_fallback))
        .with_discovery(RandomDiscovery::new(run));
    ArrayProofPlan {
        solver: SolverBackend::Z3,
        instantiation_strategy: Box::new(FullUnrollStrategy::new()),
        strategy: Box::new(
            Abstract::new(run.depth, run.run_ic3ia, policy, true)
                .with_artifact_capture(run.build_array_artifact_capture())
                .with_theory_selection(TheorySelection::Explicit(vec![Theory::Array]))
                .with_property_check_mode(PropertyCheckMode::Assumptions),
        ),
        conditional_history: None,
    }
}

struct RandomDiscovery {
    options: RandomOptions,
    no_fallback: bool,
    rng: StdRng,
    session: InstantiationSession,
    input: Option<String>,
    source: Option<String>,
    log: Option<File>,
}

impl RandomDiscovery {
    fn new(run: &YardbirdOptions) -> Self {
        Self {
            options: run.random.clone(),
            no_fallback: run.no_guided_fallback,
            rng: StdRng::seed_from_u64(run.random.random_seed),
            session: Default::default(),
            input: run.filename.clone(),
            source: None,
            log: None,
        }
    }

    fn record(&mut self, context: &DiscoveryContext<'_>, mut record: Value) -> anyhow::Result<()> {
        if self.log.is_none() {
            let path = self
                .options
                .random_log
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("missing random log path"))?;
            self.log = Some(OpenOptions::new().write(true).create_new(true).open(path)?);
        }
        record["schema_version"] = json!(1);
        record["policy"] = json!("random-instantiation");
        record["distribution"] = json!(DISTRIBUTION);
        record["configuration"] = json!(self.options);
        record["no_guided_fallback"] = json!(self.no_fallback);
        record["input"] = json!(self.input);
        record["depth"] = json!(context.depth);
        record["refinement_step"] = json!(context.refinement_step);
        record["model_version"] = json!(context.model_version);
        let log = self.log.as_mut().unwrap();
        serde_json::to_writer(&mut *log, &record)?;
        writeln!(log)?;
        log.flush()?;
        Ok(())
    }

    fn finish(
        &mut self,
        context: &DiscoveryContext<'_>,
        outcome: &str,
        samples: usize,
        started: Instant,
    ) -> anyhow::Result<()> {
        self.record(
            context,
            json!({"event":"episode_end", "outcome":outcome,
            "samples":samples, "api_calls":0, "elapsed_secs":started.elapsed().as_secs_f64(),
            "ordinary_fallback":!self.no_fallback && outcome != "violated",
            "installation_status":"not_observed_by_discovery"}),
        )
    }
}

impl InstanceDiscovery for RandomDiscovery {
    fn discover(
        &mut self,
        context: &DiscoveryContext<'_>,
    ) -> anyhow::Result<Vec<SymbolicInstance>> {
        let started = Instant::now();
        if self.source.is_none() {
            let path = self
                .input
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("missing VMT path"))?;
            self.source = Some(std::fs::read_to_string(path)?);
        }
        let snapshot = match self
            .session
            .capture(context, self.source.as_deref().unwrap())
        {
            Ok(snapshot) => snapshot,
            Err(error) => {
                self.record(
                    context,
                    json!({"event":"snapshot_error", "error":format!("{error:#}")}),
                )?;
                self.finish(context, "snapshot_error", 0, started)?;
                return Ok(vec![]);
            }
        };
        let sampler = ProposalSampler::new(&snapshot);
        self.record(context, json!({"event":"snapshot", "snapshot":snapshot.state(),
            "rng":"rand::rngs::StdRng", "eligible_axioms":sampler.schemas.iter().map(|s| &s.id).collect::<Vec<_>>(),
            "domain_sizes":sampler.domains.iter().map(|(sort, terms)| (*sort, terms.len())).collect::<BTreeMap<_,_>>()}))?;
        for attempt in 1..=self.options.random_samples {
            let Some(proposal) = sampler.sample(&mut self.rng) else {
                self.finish(context, "no_eligible_axiom", 0, started)?;
                return Ok(vec![]);
            };
            let (feedback, instance) = validate(context, snapshot.resolve(&proposal)?);
            self.record(context, json!({"event":"attempt_result", "attempt":attempt,
                "proposal":proposal, "feedback":feedback, "accepted_instances":usize::from(instance.is_some())}))?;
            if let Some(instance) = instance {
                self.finish(context, "violated", attempt, started)?;
                return Ok(vec![instance]);
            }
        }
        self.finish(
            context,
            "budget_exhausted",
            self.options.random_samples,
            started,
        )?;
        Ok(vec![])
    }
}

#[cfg(test)]
mod tests;
