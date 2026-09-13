use std::{cell::RefCell, collections::HashMap, rc::Rc, time::Instant};

use log::{debug, trace};

use crate::{
    auxiliary_synthesis::ArrayConflictRecord,
    cost_functions::YardbirdCostFunction,
    instantiation_provenance::InstantiationProvenance,
    profiling::ArrayProfilingCollector,
    theories::array::{
        array_axioms::{expr_to_term, ArrayLanguage, CompiledQuantifiedRule},
        array_grounding::{groundings, instantiate_pattern, GroundContext, GroundSubstitution},
        array_term_extractor::ArrayTermExtractor,
        instantiation_candidate::{
            InstantiationCandidate, InstantiationGrounding, SelectionHistoryDecision,
        },
    },
    training::canonical_term_hash,
};

fn trace_conflicts_enabled() -> bool {
    log::log_enabled!(log::Level::Trace)
}

fn trace_conflicts(message: impl AsRef<str>) {
    trace!("[yardbird::conflict-trace] {}", message.as_ref());
}

#[derive(Clone, Copy, Debug, Default)]
pub struct ArrayArtifactCapture {
    pub decisions: bool,
    pub instantiation_provenance: bool,
    pub conflicts: bool,
}

/// Demand for usable candidates; rejected proposals do not consume the budget.
pub(crate) struct CandidateDemand<'a> {
    pub budget: usize,
    pub accept: &'a mut dyn FnMut(&mut InstantiationCandidate) -> anyhow::Result<bool>,
}

fn round_robin<I: Iterator>(streams: impl IntoIterator<Item = I>) -> impl Iterator<Item = I::Item> {
    let mut queue = streams
        .into_iter()
        .collect::<std::collections::VecDeque<_>>();
    std::iter::from_fn(move || loop {
        let mut stream = queue.pop_front()?;
        if let Some(item) = stream.next() {
            queue.push_back(stream);
            return Some(item);
        }
    })
}

pub struct ArrayRuleInstantiatorOptions {
    pub refinement_step: u32,
    pub depth: u16,
    pub artifact_capture: ArrayArtifactCapture,
    pub profiling: Option<Rc<RefCell<ArrayProfilingCollector>>>,
}

pub struct ArrayRuleInstantiator<CF>
where
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    candidates: Vec<InstantiationCandidate>,
    selection_history: Vec<SelectionHistoryDecision>,
    artifact_capture: ArrayArtifactCapture,
    next_instantiation_ordinal: usize,
    pub cost_fn: CF,
    extractor: Rc<ArrayTermExtractor<CF>>,
    refinement_step: u32,
    depth: u16,
    profiling: Option<Rc<RefCell<ArrayProfilingCollector>>>,
}

impl<CF> ArrayRuleInstantiator<CF>
where
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    pub fn new(
        cost_fn: CF,
        extractor: ArrayTermExtractor<CF>,
        options: ArrayRuleInstantiatorOptions,
    ) -> Self {
        let ArrayRuleInstantiatorOptions {
            refinement_step,
            depth,
            artifact_capture,
            profiling,
        } = options;
        Self {
            candidates: vec![],
            selection_history: vec![],
            artifact_capture,
            next_instantiation_ordinal: 0,
            cost_fn,
            extractor: Rc::new(extractor),
            refinement_step,
            depth,
            profiling,
        }
    }

    pub(crate) fn into_candidates(mut self) -> Vec<InstantiationCandidate> {
        let latest_selection = self
            .selection_history
            .into_iter()
            .map(|decision| (decision.decision_key, decision.chosen_term_hash))
            .collect::<HashMap<_, _>>();
        for candidate in &mut self.candidates {
            for decision in &mut candidate.selection_history {
                if let Some(chosen_term_hash) = latest_selection.get(&decision.decision_key) {
                    decision.chosen_term_hash = chosen_term_hash.clone();
                }
            }
        }
        self.candidates
    }

    fn record_selection_history(&mut self, decisions: &[SelectionHistoryDecision]) {
        self.selection_history.extend_from_slice(decisions);
    }
}

impl<CF> ArrayRuleInstantiator<CF>
where
    CF: YardbirdCostFunction<ArrayLanguage>,
{
    pub(crate) fn instantiate_matches<N>(
        &mut self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        rules: &[CompiledQuantifiedRule<N>],
        pending: Vec<super::quantified_search::RuleMatch>,
        mut demand: Option<CandidateDemand<'_>>,
    ) -> anyhow::Result<()>
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        let first_round = pending.len();
        let streams = pending
            .into_iter()
            .map(|matched| {
                let super::quantified_search::RuleMatch {
                    rule_index,
                    root,
                    substitution: subst,
                    model_violation_verified,
                } = matched;
                let rule = &rules[rule_index];
                let profiling = self.profiling.is_some();
                let mut choices = groundings(
                    rule.trigger(),
                    root,
                    subst,
                    egraph,
                    self.extractor.clone(),
                    GroundContext::new(
                        self.artifact_capture.decisions,
                        rule.metadata().name(),
                        rule.metadata().category(),
                    ),
                );
                std::iter::from_fn(move || {
                    let start = profiling.then(Instant::now);
                    let grounding = choices.next()?;
                    Some((
                        rule_index,
                        root,
                        grounding,
                        model_violation_verified,
                        start.map(|start| start.elapsed()).unwrap_or_default(),
                    ))
                })
            })
            .collect::<Vec<_>>();
        let mut work = round_robin(streams);
        let budget = demand.as_ref().map(|demand| demand.budget);
        let mut visit =
            |(rule_index, root, grounding, verified, grounding_time)| -> anyhow::Result<usize> {
                let Some(mut candidate) = self.instantiate_grounding(
                    egraph,
                    &rules[rule_index],
                    root,
                    grounding,
                    grounding_time,
                ) else {
                    return Ok(0);
                };
                candidate.model_violation_verified = verified;
                let accepted = if let Some(demand) = demand.as_mut() {
                    (demand.accept)(&mut candidate)?
                } else {
                    true
                };
                self.candidates.push(candidate);
                Ok(usize::from(accepted))
            };
        let mut accepted = 0;
        // Preserve the existing first pass and let the whole-candidate ranker
        // compare its proposals. Only underfilled source batches explore more.
        for item in work.by_ref().take(first_round) {
            accepted += visit(item)?;
        }
        if let Some(budget) = budget {
            while accepted < budget {
                let Some(item) = work.next() else {
                    break;
                };
                accepted += visit(item)?;
            }
        }
        Ok(())
    }

    fn instantiate_grounding<N>(
        &mut self,
        egraph: &egg::EGraph<ArrayLanguage, N>,
        executable_rule: &CompiledQuantifiedRule<N>,
        root: egg::Id,
        grounding: GroundSubstitution,
        grounding_time: std::time::Duration,
    ) -> Option<InstantiationCandidate>
    where
        N: egg::Analysis<ArrayLanguage>,
    {
        let rule = executable_rule.metadata();
        let tracing = trace_conflicts_enabled();
        let searcher_ast = executable_rule.trigger();
        let apply_start = Instant::now();
        let candidate = {
            let mut decisions = grounding.decisions().to_vec();
            let mut selection_history = grounding.selection_history().to_vec();
            let used_derived_candidate = grounding.used_derived_candidate();
            let is_conflict = if let Some(consequence_ast) = executable_rule.consequence() {
                let new_rhs = instantiate_pattern(consequence_ast, &grounding)
                    .expect("Fully grounded consequence must be instantiable.");
                let rhs_eclass = egraph.lookup_expr(&new_rhs);
                if tracing {
                    let new_lhs = instantiate_pattern(searcher_ast, &grounding)
                        .expect("Fully grounded trigger must be instantiable.");
                    trace_conflicts(format!(
                        "    grounding lhs={} rhs={} lhs_eclass={} rhs_eclass={rhs_eclass:?}",
                        new_lhs, new_rhs, root
                    ));
                }
                Some(root) != rhs_eclass
            } else {
                // An arbitrary Boolean rule has no equality-union shortcut.
                // Build its formula once; batch preparation checks the model.
                true
            };
            if is_conflict {
                let instantiation = instantiate_pattern(executable_rule.formula(), &grounding)
                    .expect("Fully grounded rule formula must be instantiable.");

                let ordinal = self.next_instantiation_ordinal;
                self.next_instantiation_ordinal += 1;
                let instantiation_hash = canonical_term_hash(&instantiation);
                for decision in &mut decisions {
                    decision.decision_key =
                        format!("{}:candidate:{instantiation_hash}", decision.decision_key);
                }
                for decision in &mut selection_history {
                    decision.decision_key =
                        format!("{}:candidate:{instantiation_hash}", decision.decision_key);
                }
                self.record_selection_history(&selection_history);
                let selection_decision_keys = selection_history
                    .iter()
                    .map(|decision| decision.decision_key.clone())
                    .collect::<Vec<_>>();
                let decision_keys = if self.artifact_capture.decisions {
                    selection_decision_keys.clone()
                } else {
                    vec![]
                };
                let mut substitution = grounding
                    .variable_expressions()
                    .map(|(variable, expression)| {
                        (variable.to_string(), expr_to_term(expression.clone()))
                    })
                    .collect::<Vec<_>>();
                substitution.sort_by(|left, right| left.0.cmp(&right.0));

                let (_, substitution) = smt2parser::vmt::UnquantifiedInstantiator::rewrite_unquantified_with_substitution(
                    expr_to_term(instantiation.clone()),
                    vec![],
                    substitution,
                )
                .expect("array candidates should have a relative-frame substitution");
                let abstract_instantiation = self.extractor.abstract_instantiation_record(
                    rule.name(),
                    &instantiation,
                    decision_keys.clone(),
                    &substitution,
                );
                let abstract_instantiation_id =
                    abstract_instantiation.abstract_instantiation_id.clone();
                let cost_expression = &instantiation;
                let cost_site = "complete_instantiation_ranking";
                let cost = if let Some(profiling) = self.profiling.clone() {
                    profiling.borrow_mut().record_cost(
                        cost_site,
                        cost_expression.as_ref().len(),
                        || self.cost_fn.cost_rec(cost_expression),
                    )
                } else {
                    self.cost_fn.cost_rec(cost_expression)
                };

                let conflict = (self.artifact_capture.conflicts
                    && executable_rule.metadata().category()
                        == crate::quantified_rule::QuantifiedRuleCategory::ArrayAxiom)
                    .then(|| {
                        ArrayConflictRecord::new(
                            ordinal,
                            abstract_instantiation_id.clone(),
                            rule.name(),
                            instantiation.clone(),
                            expr_to_term(instantiation.clone()),
                            self.depth,
                            self.refinement_step,
                            cost,
                            decision_keys,
                        )
                    });
                let abstract_instantiation = self
                    .artifact_capture
                    .instantiation_provenance
                    .then_some(abstract_instantiation);
                let candidate = InstantiationCandidate {
                    rule: rule.clone(),
                    expression: instantiation.clone(),
                    cost,
                    grounding: if used_derived_candidate {
                        InstantiationGrounding::Derived
                    } else {
                        InstantiationGrounding::SourceGrounded
                    },
                    provenance: InstantiationProvenance::new(
                        abstract_instantiation_id,
                        substitution,
                    ),
                    selected: false,
                    decisions,
                    selection_history,
                    abstract_instantiation,
                    conflict,
                    group: executable_rule.group(egraph.find(root)),
                    model_violation_verified: false,
                };
                if tracing {
                    trace_conflicts(format!(
                        "    grounding conflict cost={} instantiation={}",
                        cost, instantiation
                    ));
                }
                debug!(
                    "FOUND VIOLATION (cost {}): \n{}",
                    cost,
                    instantiation.pretty(80)
                );

                if tracing {
                    trace_conflicts("    accepted instantiation candidate");
                }
                Some(candidate)
            } else {
                self.record_selection_history(&selection_history);
                if tracing {
                    trace_conflicts(format!(
                        "    grounding no conflict because rhs already maps to eclass {}",
                        root
                    ));
                }
                None
            }
        };
        if let Some(profiling) = &self.profiling {
            profiling.borrow_mut().record_rule_instantiation(
                rule.name(),
                1,
                false,
                grounding_time + apply_start.elapsed(),
            );
        }
        candidate
    }
}
