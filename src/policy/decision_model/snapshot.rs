use std::collections::{BTreeMap, HashMap};

use super::feedback::FailureSummary;
use serde::Serialize;
use serde_json::{json, Value};
use smt2parser::concrete::{Command, Sort, Term};

use crate::{
    policy::discovery::DiscoveryContext,
    terms::language::TermLanguage,
    theories::{array::instantiation_schema::ArrayInstantiationSchema, quantifiers::term_sort},
    theory_support::{ArrayTheorySupport, TheorySupport},
};

#[derive(Serialize)]
pub(super) struct CatalogueTerm {
    pub id: String,
    pub expression: String,
    pub sort: String,
    #[serde(skip)]
    pub term: Term,
}

pub(super) struct Snapshot {
    pub state: Value,
    pub terms: Vec<CatalogueTerm>,
    pub schemas: Vec<ArrayInstantiationSchema>,
}

impl Snapshot {
    pub fn capture(context: &DiscoveryContext<'_>) -> anyhow::Result<Self> {
        let types = context.smt.get_array_types();
        anyhow::ensure!(!types.is_empty(), "no abstract array types");
        anyhow::ensure!(
            types.iter().all(|(i, v)| i == "Int" && v == "Int"),
            "the first decision-model experiment supports Int-indexed, Int-valued arrays only"
        );
        let native_model = context.smt.native_model_to_string()?;
        let mut declarations = context.smt.get_refinement_declarations();
        declarations.extend(
            ArrayTheorySupport::new(types.clone())
                .get_uninterpreted_functions()
                .iter()
                .map(|f| f.to_command()),
        );
        let mut signatures: HashMap<String, (Vec<Sort>, Sort)> = HashMap::new();
        for declaration in &declarations {
            match declaration {
                Command::DeclareFun {
                    symbol,
                    parameters,
                    sort,
                } => {
                    signatures.insert(symbol.0.clone(), (parameters.clone(), sort.clone()));
                }
                Command::DefineFun { sig, .. } => {
                    signatures.insert(
                        sig.name.0.clone(),
                        (
                            sig.parameters
                                .iter()
                                .map(|(_, sort)| sort.clone())
                                .collect(),
                            sig.result.clone(),
                        ),
                    );
                }
                _ => {}
            }
        }
        // Include all supplied ground subterms and their children. No model
        // values, property relevance, cost ranking, or e-class pruning here.
        let mut ground = BTreeMap::new();
        for term in context
            .smt
            .get_all_subterms()
            .into_iter()
            .chain(context.smt.get_asserted_instantiation_terms())
        {
            collect_ground(term, &mut ground)?;
        }
        let mut terms = vec![];
        for (expression, term) in ground {
            let sort = term_sort(&term, &signatures, &HashMap::new())
                .map_err(|e| anyhow::anyhow!("cannot type catalogue term {expression}: {e}"))?;
            terms.push(CatalogueTerm {
                id: format!("t{}", terms.len()),
                expression,
                sort: TermLanguage::sort_to_name(&sort),
                term,
            });
        }
        let schemas = ArrayInstantiationSchema::all(&types)?;
        let mut declarations = declarations
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        declarations.extend(
            types
                .iter()
                .map(|(i, v)| format!("(declare-sort Array_{i}_{v} 0)")),
        );
        declarations.sort();
        declarations.dedup();
        let state = json!({
            "schema_version": 2,
            "task": "Find a complete array axiom instantiation that is false in this abstract model. Read/Write/ConstArr are uninterpreted functions in the model; their intended semantics are the offered axioms. First select an axiom using the model. A separate request then supplies the term catalogue and chooses all bindings for that selected axiom. Both stages use the same captured model. In the binding stage, select only catalogue term IDs; model universe elements are not legal substitution terms unless represented by a catalogue expression.",
            "axiom_guidance": {
                "write-does-not-overwrite": "To find a violated instance of write-does-not-overwrite, idx and c MUST evaluate to different values in the supplied model. Different term IDs or different expressions are not enough: their model values must differ. Never choose the same term for idx and c. If idx = c, the antecedent (not (= idx c)) is false and the entire implication is TRUE, so it cannot rule out this countermodel. Unequal indices are necessary but not sufficient: Read(Write(a, idx, val), c) and Read(a, c) must also evaluate to different values so that the consequent is false. Coordinate the idx and c choices with each other and the other bindings."
            },
            "model_format": "native Z3 model; preserve function defaults and uninterpreted-domain values; absent interpretations are unknown",
            "frame_notation": "x@N denotes x at absolute BMC frame N; unframed declaration signatures also apply to their framed instances",
            "depth": context.depth,
            "refinement_step": context.refinement_step,
            "model_version": context.model_version,
            "model": native_model,
            "declarations": declarations,
            "terms": terms,
            "axioms": schemas.iter().map(|s| json!({"id":s.id,"name":s.name(),"slots":s.slots,"body":s.formula})).collect::<Vec<_>>(),
            "catalogue_scope": "all current ground problem/refinement subterms and their children, deduplicated syntactically; no synthesized terms or heuristic shortlist",
            "successful_instantiations": {
                "meaning": "Previously installed instances from Jev or ordinary Yardbird refinement. Do not propose these again. These are normalized replay schemas: x+K denotes relative frame offset K, while x@N in the model/catalogue denotes absolute frame N. They are not claims of current-model violations. Choose bindings only from the current catalogue.",
                "instances": context.smt.get_instantiations().iter().map(ToString::to_string).collect::<std::collections::BTreeSet<_>>(),
            },
        });
        Ok(Self {
            state,
            terms,
            schemas,
        })
    }

    fn request_state(&self, failures: &FailureSummary, stage: &str) -> Value {
        let mut state = self.state.clone();
        state["failure_summary"] = json!(failures);
        state["decision_stage"] = json!(stage);
        state
    }

    pub fn axiom_request(&self, model: &str, failures: &FailureSummary) -> anyhow::Result<Value> {
        let mut choices = serde_json::Map::new();
        for schema in &self.schemas {
            if schema
                .slots
                .values()
                .any(|sort| !self.terms.iter().any(|t| &t.sort == sort))
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
        self.schema(id)
    }

    fn schema(&self, id: &str) -> anyhow::Result<&ArrayInstantiationSchema> {
        self.schemas
            .iter()
            .find(|s| s.id == id)
            .ok_or_else(|| anyhow::anyhow!("unknown axiom {id}"))
    }

    pub fn binding_request(
        &self,
        model: &str,
        failures: &FailureSummary,
        schema_id: &str,
    ) -> anyhow::Result<Value> {
        let schema = self.schema(schema_id)?;
        let correction = failures.instruction();
        let mut questions = serde_json::Map::new();
        for (slot, sort) in &schema.slots {
            let criteria = self
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
        let schema = self.schema(schema_id)?;
        let mut bindings = BTreeMap::new();
        for (slot, sort) in &schema.slots {
            let id = offered_choice(request, response, &format!("{}_{}", schema.id, slot))?;
            let term = self
                .terms
                .iter()
                .find(|t| t.id == id)
                .ok_or_else(|| anyhow::anyhow!("unknown term {id}"))?;
            anyhow::ensure!(
                &term.sort == sort,
                "wrong sort for {slot}: expected {sort}, got {}",
                term.sort
            );
            bindings.insert(slot.clone(), term.term.clone());
        }
        schema.instantiate(&bindings)
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

fn collect_ground(term: &Term, terms: &mut BTreeMap<String, Term>) -> anyhow::Result<()> {
    match term {
        Term::Application { arguments, .. } => {
            for argument in arguments {
                collect_ground(argument, terms)?;
            }
        }
        Term::Constant(_) | Term::QualIdentifier(_) => {}
        _ => anyhow::bail!("unsupported non-ground or unnormalized catalogue term: {term}"),
    }
    terms.insert(term.to_string(), term.clone());
    Ok(())
}
