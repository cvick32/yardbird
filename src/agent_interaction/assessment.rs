//! Bounded, read-only evidence for deciding whether an advice episode is useful.
use super::*;
use smt2parser::concrete::Term;

#[derive(Clone)]
pub(super) struct Sample {
    depth: u16,
    model: u64,
    step: u32,
    installed: u64,
    assertions: u64,
    pending: usize,
    probes: Vec<(Term, Value)>,
}
impl Sample {
    fn render(&self) -> Value {
        let probes: Vec<_> = self
            .probes
            .iter()
            .filter_map(|(term, value)| {
                let text = term.to_string();
                (text.len() <= 2048).then(|| json!({"expression":text,"value":value}))
            })
            .collect();
        json!({"depth":self.depth,"model":self.model,"refinement_step":self.step,"installed_instances":self.installed,"assertions":self.assertions,"pending_candidates":self.pending,"property_probes":probes})
    }
}

pub(super) fn sample(context: &DiscoveryContext<'_>, index: Option<&TransitionIndex>) -> Sample {
    let mut probes = Vec::new();
    if let Some(index) = index {
        let root = index.index_term(index.property(), context.depth);
        let mut todo = vec![&root];
        let mut visited = 0;
        while let Some(term) = todo.pop() {
            visited += 1;
            if visited > 32 {
                break;
            }
            {
                let value = match context.smt.eval_partial(term) {
                    Ok(crate::solver::api::ModelEvaluation::Known(v)) => {
                        json!({"known":bounded(&v)})
                    }
                    Ok(crate::solver::api::ModelEvaluation::Undetermined) => {
                        json!({"undetermined":true})
                    }
                    Err(_) => json!({"unavailable":true}),
                };
                probes.push((term.clone(), value));
            }
            if probes.len() >= 8 {
                break;
            }
            if let Term::Application { arguments, .. } = term {
                todo.extend(arguments.iter().take(8).rev());
            }
            // At most eight pending branches; this is a sample, not a trace.
            todo.truncate(8);
        }
    }
    Sample {
        depth: context.depth,
        model: context.model_version,
        step: context.refinement_step,
        installed: context.smt.get_number_instantiations_added(),
        assertions: context.smt.get_number_instantiation_assertions_added(),
        pending: context.pending.len(),
        probes,
    }
}

pub(super) fn bounded(text: &str) -> Value {
    let count = text.chars().count();
    json!({"text":text.chars().take(2048).collect::<String>(),"truncated":count>2048,"total_characters":count})
}

pub(super) fn request(
    context: &DiscoveryContext<'_>,
    recent: &std::collections::VecDeque<Sample>,
    previous: &crate::utils::SolverStatistics,
    last_assessment: &Value,
) -> (PrepareRequest, crate::utils::SolverStatistics) {
    let terms = context.smt.get_asserted_instantiation_terms();
    let stats = context.smt.get_solver_statistics();
    let total = terms.len();
    let terms: Vec<_> = terms.into_iter().rev().take(8).cloned().collect();
    let recent = recent.clone();
    let model = context.model_version;
    let depth = context.depth;
    let previous = previous.clone();
    let last_assessment = last_assessment.clone();
    let next = stats.clone();
    let prepare: PrepareRequest = Box::new(move |_, provider, _| {
        let evidence = json!({"epoch":format!("e{model}"),"depth":depth,
        "recent_models":recent.iter().map(Sample::render).collect::<Vec<_>>(),"previous_assessment":last_assessment,"recent_assertions":terms.iter().map(|t|bounded(&t.to_string())).collect::<Vec<_>>(),
        "asserted_formula_count":total,"solver_statistics":stats.to_json_value(),
        "solver_statistics_delta":stats.delta_since(&previous),
        "sampling":"At most 8 recent SAT models, 8 property syntax probes per model, and 8 latest asserted formulas. Text prefixes explicitly marked truncated. Probe equality does not establish model equivalence. More assertions do not establish proof progress. Full indexed context is available by choosing advise."});
        let history = vec![
            json!({"role":"developer","content":"Assess whether a running Yardbird verifier should keep refining symbolically or benefit from an advice episode. Verification continues during this call. Return assess with a brief public reason grounded in the sampled evidence. continue_symbolic chooses 1..1024 more SAT refinement boundaries before reassessment; advise opens full inspection and exact instantiation tools. The count starts on receipt, not on this older snapshot. If evidence is insufficient, advise permits inspection. You cannot stop or pause verification, change its policy, or declare a proof. No private reasoning transcript is requested."}),
            json!({"role":"user","content":evidence.to_string()}),
        ];
        let mut request = wire::request(provider, &history);
        request["tools"] = json!([{"type":"function","name":"assess","description":"Choose whether to continue native symbolic refinement or start an advice episode.","strict":false,
        "parameters":{"type":"object","additionalProperties":false,"required":["epoch","decision","reason","next_refinements"],"properties":{
            "epoch":{"type":"string"},"decision":{"type":"string","enum":["continue_symbolic","advise"]},
            "reason":{"type":"string","minLength":1,"maxLength":2000},"next_refinements":{"type":"integer","minimum":1,"maximum":1024}}}}]);
        Ok(request)
    });
    (prepare, next)
}
