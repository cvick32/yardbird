//! JEV-specific prompts, choice domains, and staged response decoding.
use std::collections::BTreeMap;

use super::feedback::FailureSummary;
use crate::{
    policy::{
        discovery::DiscoveryContext,
        instantiation::{InstantiationProposal, InstantiationSession, InstantiationSnapshot},
    },
    theories::array::instantiation_schema::ArrayInstantiationSchema,
};
use serde_json::{json, Value};

pub(super) struct Snapshot {
    pub state: Value,
    pub shared: InstantiationSnapshot,
}

impl Snapshot {
    pub fn capture(
        session: &mut InstantiationSession,
        context: &DiscoveryContext<'_>,
        problem_source: &str,
    ) -> anyhow::Result<Self> {
        let shared = session.capture(context, problem_source)?;
        let mut state = shared.state();
        let instructions = json!({
            "task": "Find a complete array axiom instantiation that is false in this abstract model. Read/Write/ConstArr are uninterpreted functions in the model; their intended semantics are the offered axioms. First select an axiom using the model. A separate request then supplies the term catalogue and chooses all bindings for that selected axiom. Both stages use the same captured model. In the binding stage, select only catalogue term IDs; model universe elements are not legal substitution terms unless represented by a catalogue expression.",
            "axiom_guidance": {
                "write-does-not-overwrite": "To find a violated instance of write-does-not-overwrite, idx and c MUST evaluate to different values in the supplied model. Different term IDs or different expressions are not enough: their model values must differ. Never choose the same term for idx and c. If idx = c, the antecedent (not (= idx c)) is false and the entire implication is TRUE, so it cannot rule out this countermodel. Unequal indices are necessary but not sufficient: Read(Write(a, idx, val), c) and Read(a, c) must also evaluate to different values so that the consequent is false. Coordinate the idx and c choices with each other and the other bindings."
            },
        });
        state
            .as_object_mut()
            .unwrap()
            .extend(instructions.as_object().unwrap().clone());
        // Preserve the existing JEV wire prompt while the common payload is neutral.
        state["successful_instantiations"]["meaning"] = json!("Previously installed instances from Jev or ordinary Yardbird refinement. Do not propose these again. These are normalized replay schemas: x+K denotes relative frame offset K, while x@N in the model/catalogue denotes absolute frame N. They are not claims of current-model violations. Choose bindings only from the current catalogue.");
        Ok(Self { state, shared })
    }

    fn request_state(&self, failures: &FailureSummary, stage: &str) -> Value {
        let mut state = self.state.clone();
        state["failure_summary"] = json!(failures);
        state["decision_stage"] = json!(stage);
        state
    }

    pub fn axiom_request(&self, model: &str, failures: &FailureSummary) -> anyhow::Result<Value> {
        let mut choices = serde_json::Map::new();
        for schema in &self.shared.schemas {
            if schema
                .slots
                .values()
                .any(|sort| !self.shared.terms.iter().any(|t| &t.sort == sort))
            {
                continue;
            }
            choices.insert(
                schema.id.clone(),
                json!({"name":schema.name(),"body":schema.formula,"slots":schema.slots}),
            );
        }
        anyhow::ensure!(
            !choices.is_empty(),
            "no axiom has nonempty term domains for every slot"
        );
        let mut state = self.request_state(failures, "quantifier_selection");
        // Choosing an axiom needs its semantics and the model, not the finite
        // binding vocabulary. The choices below already carry the schemas.
        for field in ["terms", "catalogue_scope", "axioms"] {
            state.as_object_mut().unwrap().remove(field);
        }
        Ok(json!({"model":model,"state":state,
            "questions":{"axiom":{"type":"choice",
                "instructions":format!("Choose an axiom for which you can find a NEW complete substitution making its entire formula FALSE in this model. This request selects only the axiom; a subsequent request will choose its bindings. {}", failures.instruction()),
                "criteria":choices}}}))
    }

    pub fn selected_axiom<'a>(
        &'a self,
        request: &Value,
        response: &Value,
    ) -> anyhow::Result<&'a ArrayInstantiationSchema> {
        let id = offered_choice(request, response, "axiom")?;
        self.shared.schema(id)
    }

    pub fn binding_request(
        &self,
        model: &str,
        failures: &FailureSummary,
        schema_id: &str,
    ) -> anyhow::Result<Value> {
        let schema = self.shared.schema(schema_id)?;
        let correction = failures.instruction();
        let mut questions = serde_json::Map::new();
        for (slot, sort) in &schema.slots {
            let criteria = self
                .shared
                .terms
                .iter()
                .filter(|t| &t.sort == sort)
                .map(|t| (t.id.clone(), Value::Null))
                .collect::<serde_json::Map<_, _>>();
            anyhow::ensure!(!criteria.is_empty(), "no terms of sort {sort} for {slot}");
            questions.insert(format!("{}_{}", schema.id, slot), json!({
                "type":"choice",
                "instructions":format!("Choose {slot} for the already selected axiom {} in state.selected_axiom. The axiom choice is fixed for this request. Each option name is a term ID in state.terms; look up its expression and sort in that shared catalogue. All offered terms have sort {sort}. Coordinate with ALL other bindings of this axiom to make its entire body false in the supplied model. {correction}", schema.id),
                "criteria":criteria,
            }));
        }
        let mut state = self.request_state(failures, "instantiation");
        state["selected_axiom"] =
            json!({"id":schema.id,"name":schema.name(),"body":schema.formula,"slots":schema.slots});
        Ok(json!({"model":model,"state":state,"questions":questions}))
    }

    pub fn proposal(
        &self,
        request: &Value,
        response: &Value,
    ) -> anyhow::Result<crate::rule_matching::candidate::SymbolicInstance> {
        // The binding response cannot change the axiom chosen by the first stage.
        let schema_id = request["state"]["selected_axiom"]["id"]
            .as_str()
            .ok_or_else(|| anyhow::anyhow!("binding request has no selected axiom"))?;
        let schema = self.shared.schema(schema_id)?;
        let mut bindings = BTreeMap::new();
        for slot in schema.slots.keys() {
            let id = offered_choice(request, response, &format!("{}_{}", schema.id, slot))?;
            bindings.insert(slot.clone(), id.to_owned());
        }
        self.shared.resolve(&InstantiationProposal {
            axiom_id: schema_id.to_owned(),
            bindings,
        })
    }

    /// Fixed order follows array constructor arguments, then the read index.
    pub fn binding_order(&self, request: &Value) -> anyhow::Result<Vec<String>> {
        let id = request["state"]["selected_axiom"]["id"]
            .as_str()
            .ok_or_else(|| anyhow::anyhow!("missing selected axiom"))?;
        let schema = self.shared.schema(id)?;
        let order = ["a", "idx", "val", "c", "b"]
            .into_iter()
            .filter(|slot| schema.slots.contains_key(*slot))
            .map(str::to_owned)
            .collect::<Vec<_>>();
        anyhow::ensure!(
            order.len() == schema.slots.len(),
            "unsupported binding order"
        );
        Ok(order)
    }

    pub fn conditional_request(
        &self,
        full: &Value,
        fixed_answers: &Value,
        slot: &str,
    ) -> anyhow::Result<Value> {
        let id = full["state"]["selected_axiom"]["id"]
            .as_str()
            .ok_or_else(|| anyhow::anyhow!("missing selected axiom"))?;
        let order = self.binding_order(full)?;
        let mut fixed = serde_json::Map::new();
        for prior in order.iter().take_while(|prior| prior.as_str() != slot) {
            let question = format!("{id}_{prior}");
            let term_id = offered_choice(full, fixed_answers, &question)?;
            let term = self
                .shared
                .terms
                .iter()
                .find(|t| t.id == term_id)
                .ok_or_else(|| anyhow::anyhow!("unknown fixed term {term_id}"))?;
            fixed.insert(
                prior.clone(),
                json!({"id":term.id,"expression":term.expression,"sort":term.sort}),
            );
        }
        let name = format!("{id}_{slot}");
        let mut question = full["questions"][&name].clone();
        anyhow::ensure!(question.is_object(), "unknown binding slot {slot}");
        question["instructions"] = json!(format!("Choose {slot} for state.selected_axiom, conditioned on state.fixed_bindings. Those earlier choices are FIXED: do not change them. Choose a term that permits a completion of the remaining bindings making the COMPLETE axiom false in this model. All terms of the required sort remain eligible. Look up term IDs in state.terms. {}", full["questions"][&name]["instructions"].as_str().unwrap_or_default()));
        let mut request = full.clone();
        request["questions"] = json!({name:question});
        request["state"]["decision_stage"] = json!("conditional_binding");
        request["state"]["fixed_bindings"] = json!(fixed);
        request["state"]["binding_order"] = json!(order);
        request["state"]["binding_slot"] = json!(slot);
        let task_field = if full["state"]["prompt_variant"] == "property-directed" {
            "binding_task"
        } else {
            "task"
        };
        request["state"][task_field] = json!("Find a complete array axiom instantiation that is false in this abstract model. Read/Write/ConstArr are uninterpreted functions whose intended semantics are given by the axioms. The axiom and state.fixed_bindings are already selected. Choose ONLY the requested binding, preserving earlier choices. Later bindings will be selected in subsequent requests. Use only catalogue term IDs; model-domain values are observations, not legal terms.");
        Ok(request)
    }
}

fn offered_choice<'a>(
    request: &Value,
    response: &'a Value,
    question: &str,
) -> anyhow::Result<&'a str> {
    let answer = &response["answers"][question];
    anyhow::ensure!(
        answer["type"] == "choice",
        "missing or non-choice answer for {question}"
    );
    let id = answer["choice"]
        .as_str()
        .ok_or_else(|| anyhow::anyhow!("missing choice for {question}"))?;
    anyhow::ensure!(
        request["questions"][question]["criteria"].get(id).is_some(),
        "unoffered choice {id} for {question}"
    );
    Ok(id)
}
