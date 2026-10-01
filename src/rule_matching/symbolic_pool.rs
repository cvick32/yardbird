//! Costing, model validation, and selection of exact symbolic theory instances.
use crate::{
    instance_installation::assertion_tracker::canonical_instantiation_key,
    policy::term_selection::{context::TermCostContext, TermCostFactory},
    problem_context::ProblemContext,
    rule_matching::{
        candidate::{
            CandidateGroup, InstantiationBatch, InstantiationCandidate, InstantiationGrounding,
            SymbolicInstance,
        },
        provenance::{CountermodelOrigin, InstantiationProvenance},
        scope::CandidateScope,
        search_context::SearchContext,
    },
    terms::language::{expr_to_term, translate_term_with_array_types, TermExpr},
};
use smt2parser::concrete::Term;
use std::{
    cell::OnceCell,
    collections::{HashMap, HashSet},
};

/// Stand-in for a partial evaluation's undetermined result. Not a real model
/// value: `Bool` prints as `true`/`false` and other sorts print as solver
/// element names, never as this literal string.
const UNDETERMINED: &str = "<undetermined>";

#[derive(Default)]
pub(crate) struct SymbolicCandidatePool {
    instances: Vec<SymbolicInstance>,
    seen: HashSet<Term>,
    pool_cache: PoolCache,
    origins: HashMap<Term, CountermodelOrigin>,
}
struct PreparedPoolCandidate {
    expression: TermExpr,
    provenance: InstantiationProvenance,
    installable_key: Option<Term>,
}

struct CachedPoolInstance {
    normalized_key: Option<Term>,
    violated: Option<bool>,
    prepared: OnceCell<Option<PreparedPoolCandidate>>,
}

/// Source normalization is fixed within one problem/depth. Only truth values
/// depend on the solver model; costs and selection are deliberately not cached.
#[derive(Default)]
struct PoolCache {
    depth: Option<u16>,
    model: Option<u64>,
    entries: Vec<CachedPoolInstance>,
    /// Unevaluated or violated entries. Satisfied entries sleep until the next
    /// model; known/pending entries stay here so eligibility can change freely.
    active: Vec<usize>,
}

impl PoolCache {
    fn refresh(
        &mut self,
        instances: &[SymbolicInstance],
        smt: &dyn ProblemContext,
        depth: u16,
        model: u64,
    ) {
        if self.depth != Some(depth) {
            *self = Self {
                depth: Some(depth),
                ..Default::default()
            };
        }
        if self.model != Some(model) {
            self.model = Some(model);
            self.active = (0..self.entries.len()).collect();
            for entry in &mut self.entries {
                entry.violated = None;
            }
        }
        for instance in &instances[self.entries.len()..] {
            self.active.push(self.entries.len());
            self.entries.push(CachedPoolInstance {
                normalized_key: smt
                    .make_unquantified_instance(instance.term.clone())
                    .map(|i| canonical_instantiation_key(i.get_term())),
                violated: None,
                prepared: OnceCell::new(),
            });
        }
    }
}

impl SymbolicCandidatePool {
    #[cfg(test)]
    pub(crate) fn instances(&self) -> &[SymbolicInstance] {
        &self.instances
    }

    pub(crate) fn remember(&mut self, instances: impl IntoIterator<Item = SymbolicInstance>) {
        for instance in instances {
            if self.seen.insert(instance.term.clone()) {
                self.instances.push(instance);
            }
        }
    }

    pub(crate) fn remember_traced(
        &mut self,
        instance: SymbolicInstance,
        origin: CountermodelOrigin,
    ) {
        self.origins.entry(instance.term.clone()).or_insert(origin);
        self.remember([instance]);
    }

    /// Evaluate new entries once per model, retaining satisfied links for later
    /// models. Selection and installation use the ordinary machinery each time.
    pub(crate) fn candidates<F: TermCostFactory>(
        &mut self,
        context: &SearchContext<'_, F>,
    ) -> anyhow::Result<InstantiationBatch> {
        self.candidates_with_evaluator(context, |term| context.smt.eval_to_string(term))
    }

    pub(crate) fn candidates_partial<F: TermCostFactory>(
        &mut self,
        context: &SearchContext<'_, F>,
    ) -> anyhow::Result<InstantiationBatch> {
        self.candidates_with_evaluator(context, |term| {
            Ok(context
                .smt
                .eval_partial(term)?
                .as_known()
                // `candidates_with_evaluator` only ever compares this string
                // against the literal "false"/"true", never displays or
                // stores it, so a stand-in here is safe as long as it can't
                // equal a real model value the solver would print for a
                // Boolean or an uninterpreted-sort element.
                .unwrap_or(UNDETERMINED)
                .to_owned())
        })
    }

    fn candidates_with_evaluator<F: TermCostFactory>(
        &mut self,
        context: &SearchContext<'_, F>,
        mut evaluate: impl FnMut(&Term) -> anyhow::Result<String>,
    ) -> anyhow::Result<InstantiationBatch> {
        let types = context.smt.get_array_types();
        let scope = CandidateScope::AllCandidates;
        let mut cost: Option<F> = None;
        self.pool_cache.refresh(
            &self.instances,
            context.smt,
            context.depth,
            context.model_version,
        );
        let mut known = context
            .smt
            .get_instantiations()
            .iter()
            .map(canonical_instantiation_key)
            .collect::<HashSet<_>>();
        known.extend(context.pending_instances.iter().cloned());
        let mut batch = InstantiationBatch::default();
        let mut active = Vec::with_capacity(self.pool_cache.active.len());
        let mut installable_keys = HashMap::new();
        for &i in &self.pool_cache.active {
            let instance = &self.instances[i];
            let entry = &mut self.pool_cache.entries[i];
            let Some(key) = &entry.normalized_key else {
                continue;
            };
            if known.contains(key) {
                active.push(i);
                continue;
            }
            let violated = match entry.violated {
                Some(violated) => violated,
                None => {
                    let violated = evaluate(&instance.term)?.trim() == "false";
                    entry.violated = Some(violated);
                    violated
                }
            };
            if !violated {
                continue;
            }
            let Some(prepared) = entry.prepared.get_or_init(|| {
                let expression = translate_term_with_array_types(instance.term.clone(), &types)?;
                let (_, bindings) = smt2parser::vmt::UnquantifiedInstantiator::rewrite_unquantified_with_substitution(
                    instance.term.clone(), vec![], instance.bindings.clone(),
                )?;
                // Preserve the batch's expression-based installation key even
                // when translation changes the original SMT syntax.
                let installable_key = if expr_to_term(expression.clone()) == instance.term {
                    Some(key.clone())
                } else {
                    context.installable_expression(&expression)
                };
                Some(PreparedPoolCandidate {
                    provenance: InstantiationProvenance::new(
                        format!("obligation:{}:{}", instance.rule.name(), crate::training::canonical_term_hash(&expression)),
                        bindings,
                    ),
                    expression,
                    installable_key,
                })
            }) else {
                continue;
            };
            active.push(i);
            installable_keys.insert(
                prepared.expression.clone(),
                prepared.installable_key.clone(),
            );
            let cost = cost.get_or_insert_with(|| {
                context.term_cost(
                    &TermCostContext::from_problem(context.smt, &Default::default(), scope),
                    context.depth as u32,
                )
            });
            batch.candidates.push(InstantiationCandidate {
                rule: instance.rule.clone(),
                cost: cost.cost_rec(&prepared.expression),
                provenance: prepared
                    .provenance
                    .clone()
                    .with_countermodel_origin(self.origins.get(&instance.term).cloned()),
                expression: prepared.expression.clone(),
                grounding: InstantiationGrounding::Derived,
                selected: false,
                decisions: vec![],
                selection_history: vec![],
                abstract_instantiation: None,
                conflict: None,
                group: CandidateGroup::Rule,
                model_violation_verified: true,
            });
        }
        // Commit compaction only after all evaluations succeed. An evaluation
        // error must leave unevaluated entries available for a retry.
        self.pool_cache.active = active;
        batch.prepare_with_ranker(
            scope,
            &known,
            context.allowance.winners,
            context.ranker,
            evaluate,
            |c| installable_keys.get(&c.expression).cloned().flatten(),
        )?;
        if let Some(profile) = &context.profiling {
            let mut p = profile.borrow_mut();
            p.add_counter("obligation_retained_instances", self.instances.len() as u64);
            p.add_counter(
                "obligation_violated_instances",
                batch.candidates.len() as u64,
            );
            p.add_counter(
                "obligation_selected_instances",
                batch.selected().count() as u64,
            );
        }
        Ok(batch)
    }
}
