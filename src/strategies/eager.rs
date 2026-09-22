//! Strategy-independent eager execution through ordinary instance installation.
use std::{collections::HashSet, marker::PhantomData, time::Instant};

use crate::{
    instance_installation::assertion_tracker::canonical_instantiation_key,
    policy::{
        eager::{order, EagerInstantiation},
        term_selection::TermCostFactory,
    },
    problem_context::ProblemContext,
    rule_matching::provenance::InstantiationProvenance,
    theories::array::eager_source::EagerSource,
    training::{canonical_term_hash, AbstractInstantiationRecord},
    utils::{SolverStatistics, StatisticsValue},
};

pub trait InstanceSeeder {
    fn configure_vmt(&mut self, model: &smt2parser::vmt::VMTModel, abstract_arrays: bool);
    fn configure_smtlib(
        &mut self,
        problem: &crate::smtlib_problem::SMTLIBProblem,
        abstract_arrays: bool,
    );
    fn seed(&mut self, smt: &mut dyn ProblemContext) -> anyhow::Result<()>;
    fn add_statistics(&self, statistics: &mut SolverStatistics);
    fn take_records(&mut self) -> Vec<AbstractInstantiationRecord>;
}

pub(crate) struct CostGuidedSeeder<F: TermCostFactory> {
    cost_config: F::Config,
    config: EagerInstantiation,
    records: Vec<AbstractInstantiationRecord>,
    seeded: bool,
    source: Option<EagerSource>,
    abstract_arrays: bool,
    candidates: u64,
    selected: u64,
    assertions: u64,
    elapsed: f64,
    marker: PhantomData<F>,
}

impl<F: TermCostFactory> CostGuidedSeeder<F> {
    pub(crate) fn new(cost_config: F::Config, config: EagerInstantiation) -> Self {
        Self {
            cost_config,
            config,
            records: vec![],
            seeded: false,
            source: None,
            abstract_arrays: false,
            candidates: 0,
            selected: 0,
            assertions: 0,
            elapsed: 0.0,
            marker: PhantomData,
        }
    }
}

impl<F: TermCostFactory> InstanceSeeder for CostGuidedSeeder<F> {
    fn configure_vmt(&mut self, model: &smt2parser::vmt::VMTModel, abstract_arrays: bool) {
        *self = Self::new(self.cost_config.clone(), self.config);
        self.source = Some(EagerSource::vmt(model));
        self.abstract_arrays = abstract_arrays;
    }

    fn configure_smtlib(
        &mut self,
        problem: &crate::smtlib_problem::SMTLIBProblem,
        abstract_arrays: bool,
    ) {
        *self = Self::new(self.cost_config.clone(), self.config);
        self.source = Some(EagerSource::smtlib(problem));
        self.abstract_arrays = abstract_arrays;
    }

    fn seed(&mut self, smt: &mut dyn ProblemContext) -> anyhow::Result<()> {
        if self.seeded {
            return Ok(());
        }
        anyhow::ensure!(smt.supports_eager_instantiation(),
            "eager instantiation requires a model-independent installer; use full-unroll or no-unroll-on-loop instead of schema-batch");
        let source = self.source.take().ok_or_else(|| {
            anyhow::anyhow!(
                "eager instantiation requires original source capture before strategy configuration"
            )
        })?;
        self.seeded = true;
        let start = Instant::now();
        let seeds = crate::theories::array::eager::generate::<F>(
            &source.vocabulary,
            &self.cost_config,
            self.config,
            self.abstract_arrays,
        );
        self.candidates = seeds.len() as u64;
        let mut known = HashSet::new();
        let mut eligible = Vec::new();
        for seed in seeds {
            let hash = canonical_term_hash(&seed.normalized);
            let id = format!("eager:{}:0:{hash}", seed.rule);
            let provenance = InstantiationProvenance::new(id.clone(), seed.bindings);
            let Some(request) = source.make_request(seed.term, provenance) else {
                continue;
            };
            let key = canonical_instantiation_key(request.inst.get_term());
            if !known.insert(key) {
                continue;
            }
            let record = AbstractInstantiationRecord {
                abstract_instantiation_id: id,
                term: request.inst.get_term().to_string(),
                term_hash: hash,
                axiom_name: seed.rule,
                bmc_depth: 0,
                refinement_step: 0,
                decision_keys: vec![],
                substitution: request.provenance.as_ref().unwrap().relative_substitution(),
                was_selected: true,
                indexed_assertions_attempted: 0,
                indexed_assertions_added: 0,
                indexed_assertions_deduplicated: 0,
                helper_assertions_attempted: 0,
                helper_assertions_added: 0,
                helper_assertions_deduplicated: 0,
                in_unsat_core: false,
            };
            eligible.push((
                seed.cost,
                seed.family,
                seed.normalized.to_string(),
                (request, record),
            ));
        }
        let selected = order(
            eligible,
            self.config.max_instances,
            self.config.diversify_ties,
        );
        let selected_count = selected.len();
        for (request, mut record) in selected {
            let result = smt.add_instantiation(request);
            record.indexed_assertions_attempted = result.indexed_assertions_attempted;
            record.indexed_assertions_added = result.indexed_assertions_added;
            record.indexed_assertions_deduplicated = result.indexed_assertions_deduplicated;
            record.helper_assertions_attempted = result.helper_assertions_attempted;
            record.helper_assertions_added = result.helper_assertions_added;
            record.helper_assertions_deduplicated = result.helper_assertions_deduplicated;
            self.selected += 1;
            self.assertions += result.solver_assertions_added();
            self.records.push(record);
        }
        let elapsed = start.elapsed().as_secs_f64();
        self.elapsed = elapsed;
        log::info!(
            "Eager instantiation: selected={selected_count} assertions={} time={elapsed:.6}s",
            self.assertions
        );
        Ok(())
    }

    fn add_statistics(&self, statistics: &mut SolverStatistics) {
        for (name, value) in [
            ("passes", u64::from(self.seeded)),
            ("candidates", self.candidates),
            ("instances", self.selected),
            ("assertions", self.assertions),
        ] {
            statistics.insert(format!("eager.{name}"), StatisticsValue::UInt(value));
        }
        statistics.insert(
            "eager.time_secs".into(),
            StatisticsValue::Double(self.elapsed),
        );
    }

    fn take_records(&mut self) -> Vec<AbstractInstantiationRecord> {
        std::mem::take(&mut self.records)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        instance_installation::full_unroll::FullUnrollStrategy,
        policy::term_selection::array::ArrayAstSize,
        solver::SolverCheckResult,
        strategies::{Abstract, ConcreteArrayZ3, ProofStrategy, RefinementState},
        vmt_bmc_session::VmtBmcSession,
        SolverBackend, YardbirdPolicy,
    };
    use smt2parser::{concrete::SyntaxBuilder, vmt::VMTModel, CommandStream};

    const INPUT: &str = r#"
        (declare-fun a () (Array Int Int))
        (define-fun a.link () (Array Int Int) (! a :next a.next))
        (declare-fun i () Int)
        (define-fun i.link () Int (! i :next i.next))
        (declare-fun j () Int)
        (define-fun j.link () Int (! j :next j.next))
        (declare-fun v () Int)
        (define-fun v.link () Int (! v :next v.next))
        (define-fun init () Bool (! true :init true))
        (define-fun trans () Bool (!
          (and (= a.next a) (= i.next i) (= j.next j) (= v.next v)) :trans true))
        (define-fun prop () Bool (!
          (= (select (store a i v) j) (ite (= i j) v (select a j))) :invar-property 0))
    "#;

    fn source_model() -> VMTModel {
        VMTModel::checked_from(
            CommandStream::new(INPUT.as_bytes(), SyntaxBuilder, None)
                .collect::<Result<Vec<_>, _>>()
                .unwrap(),
        )
        .unwrap()
    }

    fn normalized_assertions(session: &VmtBmcSession) -> std::collections::BTreeSet<String> {
        use smt2parser::{concrete::Term, vmt::array_abstractor::ArrayAbstractor};
        session
            .get_tracked_labels()
            .iter()
            .map(|record| {
                let mut abstractor = ArrayAbstractor::default();
                for frame in 0..=2 {
                    abstractor
                        .variable_types
                        .insert(format!("a@{frame}"), ("Int".into(), "Int".into()));
                }
                let term = record
                    .term
                    .parse::<Term>()
                    .unwrap()
                    .accept(&mut abstractor)
                    .unwrap();
                canonical_instantiation_key(&term).to_string()
            })
            .collect()
    }

    fn fixture(
        native: bool,
        enabled: bool,
    ) -> (
        Box<dyn ProofStrategy<'static, RefinementState>>,
        VmtBmcSession,
    ) {
        fixture_for_input(native, enabled, INPUT)
    }

    fn fixture_for_input(
        native: bool,
        enabled: bool,
        input: &str,
    ) -> (
        Box<dyn ProofStrategy<'static, RefinementState>>,
        VmtBmcSession,
    ) {
        let policy = YardbirdPolicy::<ArrayAstSize>::new(());
        let policy = if enabled {
            policy.with_eager_instantiation(EagerInstantiation::default())
        } else {
            policy
        };
        let mut strategy: Box<dyn ProofStrategy<'static, RefinementState>> = if native {
            Box::new(ConcreteArrayZ3::new(false).with_eager_policy(&policy))
        } else {
            Box::new(Abstract::new(2, false, policy, false))
        };
        let commands = CommandStream::new(input.as_bytes(), SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let model = strategy.configure_model(VMTModel::checked_from(commands).unwrap());
        let session = VmtBmcSession::new(
            &model,
            &strategy,
            SolverBackend::Z3,
            true,
            Box::new(FullUnrollStrategy::new()),
            false,
            None,
        )
        .unwrap();
        (strategy, session)
    }

    #[test]
    fn eager_seeds_are_installed_before_any_model_in_both_encodings_and_replayed() {
        let mut expected = None;
        for native in [false, true] {
            let (mut strategy, mut session) = fixture(native, true);
            assert!(!session.has_model());
            strategy.seed_instances(&mut session).unwrap();
            assert!(!session.has_model());
            let before = session.get_number_instantiation_assertions_added();
            assert!(before > 0);
            assert!(session.get_instantiations().len() <= 32);
            let schemas = session.get_instantiations();
            let records = strategy.take_eager_artifacts();
            assert!(!records.is_empty());
            assert!(records
                .iter()
                .all(|r| r.bmc_depth == 0 && !r.substitution.is_empty()));
            assert_eq!(session.check_property(), SolverCheckResult::Unsat);
            strategy.seed_instances(&mut session).unwrap();
            assert_eq!(session.get_number_instantiation_assertions_added(), before);
            for depth in 1..=2 {
                session.unroll(depth);
                let after_replay = session.get_number_instantiation_assertions_added();
                assert!(after_replay > before);
                strategy.seed_instances(&mut session).unwrap();
                assert_eq!(
                    session.get_number_instantiation_assertions_added(),
                    after_replay
                );
                assert_eq!(session.get_instantiations(), schemas);
                assert!(strategy.take_eager_artifacts().is_empty());
                assert_eq!(session.check_property(), SolverCheckResult::Unsat);
            }
            let assertions = normalized_assertions(&session);
            if let Some(expected) = &expected {
                assert_eq!(&assertions, expected);
            }
            expected = Some(assertions);
        }
    }

    #[test]
    fn transition_only_seeds_are_selected_initially_and_wait_for_their_first_frame() {
        let input = INPUT
            .replace(
                "(and (= a.next a) (= i.next i) (= j.next j) (= v.next v))",
                "(= a.next (store a i.next v.next))",
            )
            .replace(
                "(= (select (store a i v) j) (ite (= i j) v (select a j)))",
                "true",
            );
        for native in [false, true] {
            let (mut strategy, mut session) = fixture_for_input(native, true, &input);
            strategy.seed_instances(&mut session).unwrap();
            let schemas = session.get_instantiations();
            assert!(
                !schemas.is_empty(),
                "transition vocabulary must be scanned before any unrolling"
            );
            assert_eq!(session.get_number_instantiation_assertions_added(), 0);
            assert!(!session.has_model());
            assert!(!strategy.take_eager_artifacts().is_empty());
            session.unroll(1);
            assert!(session.get_number_instantiation_assertions_added() > 0);
            strategy.seed_instances(&mut session).unwrap();
            assert_eq!(session.get_instantiations(), schemas);
            assert!(strategy.take_eager_artifacts().is_empty());
        }
    }

    #[test]
    fn no_unroll_replays_eager_seeds_but_not_refinement_instances() {
        use crate::instance_installation::{
            no_unroll_on_loop::NoUnrollOnLoop, request::InstantiationRequest,
        };
        let (mut strategy, _) = fixture(false, true);
        let model = strategy.configure_model(source_model());
        let mut session = VmtBmcSession::new(
            &model,
            &strategy,
            SolverBackend::Z3,
            true,
            Box::new(NoUnrollOnLoop::new()),
            false,
            None,
        )
        .unwrap();
        strategy.seed_instances(&mut session).unwrap();
        let instance = session
            .make_unquantified_instance("(= i@0 i@0)".parse().unwrap())
            .unwrap();
        session.add_instantiation(InstantiationRequest::untracked(instance));
        session.unroll(1);
        let assertions = normalized_assertions(&session);
        assert!(assertions.contains("(= i@0 i@0)"));
        assert!(!assertions.contains("(= i@1 i@1)"));
        assert_eq!(session.check_property(), SolverCheckResult::Unsat);
    }

    #[test]
    fn eager_native_and_abstract_candidates_have_identical_normalized_costs() {
        let config = EagerInstantiation {
            max_candidates: 7,
            max_instances: 2,
            diversify_ties: true,
        };
        let source = EagerSource::vmt(&source_model());
        let describe = |abstract_arrays| {
            crate::theories::array::eager::generate::<ArrayAstSize>(
                &source.vocabulary,
                &(),
                config,
                abstract_arrays,
            )
            .into_iter()
            .map(|s| (s.normalized.to_string(), s.cost, s.family))
            .collect::<Vec<_>>()
        };
        let expected = describe(true);
        assert!(!expected.is_empty());
        assert!(expected.len() <= 7);
        assert_eq!(describe(false), expected);
        let mut seeder = CostGuidedSeeder::<ArrayAstSize>::new((), config);
        seeder.configure_vmt(&source_model(), true);
        let (_, mut session) = fixture(false, false);
        seeder.seed(&mut session).unwrap();
        assert!(session.get_instantiations().len() <= 2);
    }

    #[test]
    fn eager_rejects_model_dependent_installation_before_a_check() {
        use crate::instance_installation::schema_batch::SchemaBatchStrategy;
        let (mut strategy, _) = fixture(false, true);
        let commands = CommandStream::new(INPUT.as_bytes(), SyntaxBuilder, None)
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let model = strategy.configure_model(VMTModel::checked_from(commands).unwrap());
        let mut session = VmtBmcSession::new(
            &model,
            &strategy,
            SolverBackend::Z3,
            false,
            Box::new(SchemaBatchStrategy::new()),
            false,
            None,
        )
        .unwrap();
        assert!(strategy
            .seed_instances(&mut session)
            .unwrap_err()
            .to_string()
            .contains("model-independent"));
        assert!(!session.has_model());
        assert!(session.get_instantiations().is_empty());
    }

    #[test]
    fn eager_disabled_preserves_the_unseeded_initial_query() {
        let (mut strategy, mut session) = fixture(false, false);
        strategy.seed_instances(&mut session).unwrap();
        assert!(session.get_instantiations().is_empty());
        assert_eq!(session.check_property(), SolverCheckResult::Sat);
    }
}
