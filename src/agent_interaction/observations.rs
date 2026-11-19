//! Read-only action context. Retrieval never performs relational matching or
//! turns a model observation into a premise asserted to the solver.
use crate::{
    countermodel::{CountermodelTrace, TraceReason},
    policy::{
        discovery::DiscoveryContext,
        instantiation::{InstantiationSession, InstantiationSnapshot},
    },
    transition_index::TransitionIndex,
};
use serde_json::{json, Value};
use smt2parser::concrete::Term;
use std::collections::BTreeMap;

pub(crate) struct Observations {
    pub records: BTreeMap<String, Value>,
    pub roots: Vec<String>,
    actions: BTreeMap<String, (String, u16)>,
    cursors: BTreeMap<String, usize>,
    epoch: String,
    index: TransitionIndex,
    pub work: usize,
}

fn evaluation(context: &DiscoveryContext<'_>, term: &Term) -> Value {
    match context.smt.eval_partial(term) {
        Ok(crate::solver::api::ModelEvaluation::Known(value)) => {
            json!({"status":"known","value":value})
        }
        Ok(_) => json!({"status":"undetermined","value":null}),
        Err(_) => json!({"status":"error","value":null}),
    }
}
fn record(id: &str, kind: &str, expression: String, frame: Option<u16>, data: Value) -> Value {
    json!({"id":id,"kind":kind,"expression":expression,"sort":"Bool","frame":frame,"links":{},"data":data})
}

type NodeEvidence = (Value, Option<(String, u16, Value)>);

pub(super) struct TraceInput {
    index: TransitionIndex,
    trace: CountermodelTrace,
    nodes: Vec<NodeEvidence>,
}

impl TraceInput {
    pub(super) fn collect(
        index: TransitionIndex,
        context: &DiscoveryContext<'_>,
        work: usize,
    ) -> Self {
        let trace = crate::countermodel::trace_refinement(
            &index,
            &context.smt.get_array_types(),
            context.depth,
            context.model_version,
            work,
            |t| context.smt.eval_partial(t),
            context.quantifiers.map(|(p, _)| p),
            crate::policy::effort::GuidanceTransitionOrder::PredecessorOnly,
        );
        let nodes = trace
            .nodes
            .iter()
            .map(|node| {
                let action = match &node.reason {
                    TraceReason::Transition {
                        frame,
                        action: Some(name),
                        ..
                    } => Some((name.clone(), *frame)),
                    TraceReason::QuantifiedTransition { frame, .. } => index
                        .selected_action(*frame, |t| {
                            context
                                .smt
                                .eval_partial(t)?
                                .as_known()
                                .map(str::to_owned)
                                .ok_or_else(|| anyhow::anyhow!("unknown action"))
                        })
                        .ok()
                        .flatten()
                        .map(|name| (name.to_owned(), *frame)),
                    _ => None,
                };
                let action = action.map(|(name, frame)| {
                    let term =
                        index.index_term(&crate::theories::quantifiers::app(&name, vec![]), frame);
                    let value = evaluation(context, &term);
                    (name, frame, value)
                });
                (evaluation(context, &node.expression), action)
            })
            .collect();
        Self {
            index,
            trace,
            nodes,
        }
    }
}

impl Observations {
    pub fn new(
        index: TransitionIndex,
        context: &DiscoveryContext<'_>,
        epoch: &str,
        catalogue: &mut InstantiationSession,
        snapshot: &mut InstantiationSnapshot,
    ) -> anyhow::Result<Self> {
        Self::from_trace(
            TraceInput::collect(index, context, 1024),
            epoch,
            catalogue,
            snapshot,
        )
    }

    pub(super) fn from_trace(
        input: TraceInput,
        epoch: &str,
        catalogue: &mut InstantiationSession,
        snapshot: &mut InstantiationSnapshot,
    ) -> anyhow::Result<Self> {
        let TraceInput {
            index,
            trace,
            nodes,
        } = input;
        let mut s = Self {
            records: BTreeMap::new(),
            roots: vec![],
            actions: BTreeMap::new(),
            cursors: BTreeMap::new(),
            epoch: epoch.into(),
            index,
            work: 0,
        };
        s.add_trace(&trace, nodes, catalogue, snapshot)?;
        Ok(s)
    }
    fn add_trace(
        &mut self,
        trace: &CountermodelTrace,
        nodes: Vec<NodeEvidence>,
        catalogue: &mut InstantiationSession,
        snapshot: &mut InstantiationSnapshot,
    ) -> anyhow::Result<()> {
        for (node, (value, action)) in trace.nodes.iter().zip(nodes) {
            let id = format!("{}:trace:{}", self.epoch, node.id);
            // Native source terms already have justified declarations; unsupported
            // syntax stays visible as an observation even when it is not a term input.
            let _ = catalogue.admit(snapshot, std::slice::from_ref(&node.expression), 4096);
            let reason = serde_json::to_value(&node.reason)?;
            let status = serde_json::to_value(&node.status)?;
            let mut r = record(
                &id,
                "trace",
                node.expression.to_string(),
                None,
                json!({"reason":reason["kind"],"status":status["kind"],"evaluation":value,"source_ref":null}),
            );
            if let Some(parent) = node.parent {
                r["links"]["parent"] = json!([format!("{}:trace:{parent}", self.epoch)]);
            } else {
                self.roots.push(id.clone());
            }
            if let Some((name, frame, evidence)) = action {
                let aid = format!("{}:action:{frame}:{name}", self.epoch);
                r["links"]["actions"] = json!([aid]);
                if !self.actions.contains_key(&aid) {
                    self.add_action(&aid, &name, frame, evidence, catalogue, snapshot)?;
                    self.actions.insert(aid, (name, frame));
                }
            }
            // Include exact captures through catalogue references, rather than
            // asking the client to recover them from uninterpreted model values.
            r["links"]["terms"] = json!(snapshot
                .terms
                .iter()
                .filter(|t| t.expression == node.expression.to_string())
                .map(|t| t.id.clone())
                .collect::<Vec<_>>());
            self.records.insert(id, r);
        }
        Ok(())
    }
    fn add_action(
        &mut self,
        id: &str,
        name: &str,
        frame: u16,
        evidence: Value,
        catalogue: &mut InstantiationSession,
        snapshot: &mut InstantiationSnapshot,
    ) -> anyhow::Result<()> {
        let action = self
            .index
            .index_term(&crate::theories::quantifiers::app(name, vec![]), frame);
        let mut arguments = BTreeMap::new();
        let mut updates = vec![];
        for (i, update) in self.index.action_updates(name).enumerate() {
            let term = self.index.index_term(
                &crate::theories::quantifiers::app(
                    "=",
                    vec![update.target_expression.clone(), update.value.clone()],
                ),
                frame,
            );
            let uid = format!("{id}:update:{i}");
            self.records.insert(
                uid.clone(),
                record(
                    &uid,
                    "source",
                    term.to_string(),
                    Some(frame),
                    json!({"source_kind":"transition","parent_ref":null}),
                ),
            );
            updates.push(uid);
            if catalogue
                .admit(snapshot, std::slice::from_ref(&term), 4096)
                .is_ok()
            {
                let mut pending = vec![&term];
                let mut seen = std::collections::HashSet::new();
                while let Some(subterm) = pending.pop() {
                    if !seen.insert(subterm) {
                        continue;
                    }
                    if let Some(entry) = snapshot.terms.iter().find(|entry| &entry.term == subterm)
                    {
                        arguments.insert(
                            format!("update_{i}_term_{}", seen.len() - 1),
                            entry.id.clone(),
                        );
                    }
                    if let Term::Application { arguments, .. } = subterm {
                        pending.extend(arguments.iter().rev());
                    }
                }
            }
        }
        self.records.insert(id.into(),record(id,"action",action.to_string(),Some(frame),json!({"arguments":arguments,"prerequisite_refs":[],"update_refs":updates,"selection_evidence":evidence,"requirements_expanded":false})));
        Ok(())
    }
    pub fn expand(
        &mut self,
        id: &str,
        budget: usize,
        context: &DiscoveryContext<'_>,
        catalogue: &mut InstantiationSession,
        snapshot: &mut InstantiationSnapshot,
    ) -> anyhow::Result<(Vec<Value>, Vec<String>, usize, bool)> {
        self.expand_with(
            id,
            budget,
            |term| evaluation(context, term),
            catalogue,
            snapshot,
        )
    }

    /// Sample only the live terms needed for the requested page, before the worker renders it.
    pub(super) fn expansion_values(
        &self,
        id: &str,
        budget: usize,
        context: &DiscoveryContext<'_>,
    ) -> anyhow::Result<(std::collections::HashMap<Term, Value>, usize)> {
        let (name, frame) = self
            .actions
            .get(id)
            .ok_or_else(|| anyhow::anyhow!("not an encountered action occurrence"))?;
        let mut values = std::collections::HashMap::new();
        let mut used = 0;
        let cursor = self.cursors.get(id).copied().unwrap_or(0);
        for requirement in &self.index.actions()[name].requirements[cursor..] {
            let cost = 1 + requirement.guards.len();
            if used + cost > budget {
                break;
            }
            used += cost;
            for expr in std::iter::once(&requirement.body)
                .chain(requirement.binders.iter().map(|b| &b.application))
                .chain(requirement.guards.iter().map(|g| &g.expression))
            {
                let term = self.index.index_term(expr, *frame);
                values
                    .entry(term)
                    .or_insert_with_key(|term| evaluation(context, term));
            }
        }
        Ok((values, used))
    }

    pub(super) fn expand_with(
        &mut self,
        id: &str,
        budget: usize,
        evaluate: impl Fn(&Term) -> Value,
        catalogue: &mut InstantiationSession,
        snapshot: &mut InstantiationSnapshot,
    ) -> anyhow::Result<(Vec<Value>, Vec<String>, usize, bool)> {
        let (name, frame) = self
            .actions
            .get(id)
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("not an encountered action occurrence"))?;
        let requirements = &self.index.actions()[&name].requirements;
        let cursor = self.cursors.entry(id.into()).or_default();
        let mut records = vec![];
        let mut refs = vec![];
        let mut used = 0;
        while *cursor < requirements.len() {
            let requirement = &requirements[*cursor];
            let cost = 1 + requirement.guards.len();
            if used + cost > budget {
                break;
            }
            used += cost;
            let body = self.index.index_term(&requirement.body, frame);
            let rid = format!("{id}:requirement:{}", *cursor);
            let mut r = record(
                &rid,
                "trace",
                body.to_string(),
                Some(frame),
                json!({"reason":"action_requirement","status":"exposed","evaluation":evaluate(&body),"source_ref":null}),
            );
            r["links"]["action"] = json!([id]);
            let _ = catalogue.admit(snapshot, std::slice::from_ref(&body), 4096);
            r["links"]["terms"] = json!(snapshot
                .terms
                .iter()
                .filter(|t| t.expression == body.to_string())
                .map(|t| t.id.clone())
                .collect::<Vec<_>>());
            let mut schemas = vec![];
            let mut capture_terms = vec![];
            let mut binder_refs = vec![];
            for (b, binder) in requirement.binders.iter().enumerate() {
                let schema_start = schemas.len();
                let capture_start = capture_terms.len();
                let application = self.index.index_term(&binder.application, frame);
                let _ = catalogue.admit(snapshot, std::slice::from_ref(&application), 4096);
                for schema in &snapshot.schemas {
                    if schema.name() == binder.helper {
                        schemas.push(schema.id.clone());
                    }
                }
                if let Term::Application { arguments, .. } = &application {
                    for arg in arguments {
                        if let Some(t) = snapshot
                            .terms
                            .iter()
                            .find(|t| t.expression == arg.to_string())
                        {
                            capture_terms.push(t.id.clone());
                        }
                    }
                }
                let bid = format!("{rid}:binder:{b}");
                let mut binding = record(
                    &bid,
                    "trace",
                    application.to_string(),
                    Some(frame),
                    json!({"reason":"binder_application","status":"exposed","evaluation":evaluate(&application),"source_ref":null}),
                );
                binding["links"]["schemas"] = json!(&schemas[schema_start..]);
                binding["links"]["captures"] = json!(&capture_terms[capture_start..]);
                binding["links"]["requirement"] = json!([rid]);
                self.records.insert(bid.clone(), binding.clone());
                records.push(binding);
                binder_refs.push(bid);
            }
            r["links"]["binders"] = json!(binder_refs);
            r["links"]["schemas"] = json!(schemas);
            r["links"]["captures"] = json!(capture_terms);
            let mut guards = vec![];
            for (j, guard) in requirement.guards.iter().enumerate() {
                let gid = format!("{rid}:guard:{j}");
                let term = self.index.index_term(&guard.expression, frame);
                let g = record(
                    &gid,
                    "trace",
                    term.to_string(),
                    Some(frame),
                    json!({"reason":if guard.required_value{"required_true"}else{"required_false"},"status":"observed","evaluation":evaluate(&term),"source_ref":null}),
                );
                self.records.insert(gid.clone(), g.clone());
                records.push(g);
                guards.push(gid);
            }
            r["links"]["guards"] = json!(guards);
            self.records.insert(rid.clone(), r.clone());
            records.push(r);
            refs.push(rid.clone());
            self.records.get_mut(id).unwrap()["data"]["prerequisite_refs"]
                .as_array_mut()
                .unwrap()
                .push(json!(rid));
            *cursor += 1;
        }
        let cutoff = *cursor < requirements.len();
        self.work += used;
        self.records.get_mut(id).unwrap()["data"]["requirements_expanded"] = json!(!cutoff);
        records.push(self.records[id].clone());
        Ok((records, refs, used, cutoff))
    }
}
