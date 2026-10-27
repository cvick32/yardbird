//! Frozen, provider-independent context for a single instantiation episode.
use std::collections::{BTreeMap, BTreeSet, HashMap};

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use smt2parser::concrete::{Command, Sort, Term};

use crate::{
    policy::discovery::DiscoveryContext,
    rule_matching::candidate::SymbolicInstance,
    terms::language::TermLanguage,
    theories::{array::instantiation_schema::ArrayInstantiationSchema, quantifiers::term_sort},
    theory_support::{ArrayTheorySupport, TheorySupport},
};

/// Provider responses resolve to this representation before any formula is built.
/// Term IDs are stable within a run, but only the current snapshot defines eligibility.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct InstantiationProposal {
    pub axiom_id: String,
    pub bindings: BTreeMap<String, String>,
}

#[derive(Serialize)]
pub(crate) struct CatalogueTerm {
    pub id: String,
    pub expression: String,
    pub sort: String,
    #[serde(skip)]
    pub term: Term,
}

/// Owns the full source/model/vocabulary, without provider prompts or choices.
/// Capture once per model and reuse for every attempt in that episode. Resolution
/// constructs exact theory instances; validation against the live model is separate.
pub(crate) struct InstantiationSnapshot {
    pub terms: Vec<CatalogueTerm>,
    pub schemas: Vec<ArrayInstantiationSchema>,
    model: String,
    pub(super) declarations: Vec<String>,
    pub(super) prefix: Vec<Value>,
    depth: u16,
    refinement_step: u32,
    model_version: u64,
    successful_instantiations: BTreeSet<String>,
    problem_source: String,
}

impl InstantiationSnapshot {
    pub(super) fn capture(
        context: &DiscoveryContext<'_>,
        problem_source: &str,
    ) -> anyhow::Result<Self> {
        let types = context.smt.get_array_types();
        anyhow::ensure!(!types.is_empty(), "no abstract array types");
        anyhow::ensure!(
            types.iter().all(|(i, v)| i == "Int" && v == "Int"),
            "guided instantiation supports Int-indexed, Int-valued arrays only"
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
        // Traverse whole formulas first so removing Boolean catalogue entries
        // cannot discard their integer/array descendants. No model-value,
        // property-relevance, cost-ranking, or e-class pruning here.
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
            let sort = TermLanguage::sort_to_name(&sort);
            // None of the supported Int/Int array axiom slots accept Bool.
            // This only filters substitution options, never the native model.
            if sort == "Bool" {
                continue;
            }
            terms.push(CatalogueTerm {
                id: format!("t{}", terms.len()),
                expression,
                sort,
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
        Ok(Self {
            terms,
            schemas,
            model: native_model,
            declarations,
            prefix: Vec::new(),
            depth: context.depth,
            refinement_step: context.refinement_step,
            model_version: context.model_version,
            successful_instantiations: context
                .smt
                .get_instantiations()
                .iter()
                .map(ToString::to_string)
                .collect(),
            problem_source: problem_source.to_owned(),
        })
    }

    /// Common inference payload. Adapters add instructions and their response
    /// protocol without recapturing or filtering the underlying context.
    pub fn state(&self) -> Value {
        let mut state = json!({
            "schema_version": 3,
            "model_format": "native Z3 model; preserve function defaults and uninterpreted-domain values; absent interpretations are unknown",
            "frame_notation": "x@N denotes x at absolute BMC frame N; unframed declaration signatures also apply to their framed instances",
            "depth": self.depth,
            "refinement_step": self.refinement_step,
            "model_version": self.model_version,
            "model": self.model,
            "declarations": self.declarations,
            "terms": self.terms,
            "axioms": self.schemas.iter().map(|s| json!({"id":s.id,"name":s.name(),"slots":s.slots,"body":s.formula})).collect::<Vec<_>>(),
            "catalogue_scope": "all non-Boolean current ground problem/refinement subterms, including children of Boolean formulas, deduplicated syntactically; no synthesized terms or heuristic shortlist; the full model retains Boolean interpretations",
            "successful_instantiations": {
                "meaning": "Previously installed instances from guided or ordinary Yardbird refinement. Do not propose these again. These are normalized replay schemas: x+K denotes relative frame offset K, while x@N in the model/catalogue denotes absolute frame N. They are not claims of current-model violations. Choose bindings only from the current catalogue.",
                "instances": self.successful_instantiations,
            },
        });
        state["problem"] = json!({
            "format":"VMT", "source":self.problem_source,
            "notation":"The complete original verification problem. :init marks initialization, :trans the transition relation, :invar-property the property, and :next the current/next variable mapping. For Int arrays, select/store correspond to abstract Read_Int_Int/Write_Int_Int. x@N denotes absolute frame N; next variables denote the following frame. The original problem uses array semantics; the abstract function tables may violate them."
        });
        state
    }

    /// Ordered immutable static/vocabulary blocks. Each request must carry all
    /// blocks; this is a full context representation, not a remote delta protocol.
    pub fn prefix(&self) -> &[Value] {
        &self.prefix
    }

    /// Only current-model information. No past model or provider answers persist.
    pub fn current_state(&self) -> Value {
        let mut state = self.state();
        for block in &self.prefix {
            for field in block.as_object().unwrap().keys() {
                state.as_object_mut().unwrap().remove(field);
            }
        }
        state
    }

    pub fn schema(&self, id: &str) -> anyhow::Result<&ArrayInstantiationSchema> {
        self.schemas
            .iter()
            .find(|s| s.id == id)
            .ok_or_else(|| anyhow::anyhow!("unknown axiom {id}"))
    }

    /// Resolve catalogue IDs, enforcing exact slots and sorts before grounding.
    /// No provider-supplied formula or model-domain value is accepted here.
    pub fn resolve(&self, proposal: &InstantiationProposal) -> anyhow::Result<SymbolicInstance> {
        let schema = self.schema(&proposal.axiom_id)?;
        anyhow::ensure!(
            proposal.bindings.keys().eq(schema.slots.keys()),
            "substitution must bind exactly the schema's slots"
        );
        let mut bindings = BTreeMap::new();
        for (slot, sort) in &schema.slots {
            let id = &proposal.bindings[slot];
            let term = self
                .terms
                .iter()
                .find(|t| &t.id == id)
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
