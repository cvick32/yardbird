use crate::policy::instantiation::InstantiationSnapshot;
use serde_json::{json, Value};
use std::collections::BTreeMap;

pub(crate) fn catalogue(snapshot: &InstantiationSnapshot) -> BTreeMap<String, Value> {
    let mut records = BTreeMap::new();
    for term in &snapshot.terms {
        records.insert(term.id.clone(), json!({"id":term.id,"kind":"term","expression":term.expression,"sort":term.sort,"frame":term_frame(&term.term),"links":{},"data":{"origin":{"kind":"catalogue"},"evaluation":{"status":"not_evaluated","value":null}}}));
    }
    let state = snapshot.state();
    if let Some(sources) = state["binder_sources"].as_object() {
        for (id, source) in sources {
            let kind = match source["kind"].as_str().unwrap_or("") {
                "init" | "initial" => "init",
                "trans" | "transition" => "transition",
                "property" => "property",
                _ => "axiom",
            };
            records.insert(id.clone(), json!({"id":id,"kind":"source","expression":source["formula"],"sort":null,"frame":null,"links":{},"data":{"source_kind":kind,"parent_ref":source["parent_source_id"]}}));
        }
    }
    for schema in &snapshot.schemas {
        let mut names = serde_json::Map::new();
        for key in ["capture_slots", "variable_slots"] {
            if let Some(slots) = schema.provenance[key].as_array() {
                for slot in slots {
                    if let Some(id) = slot["slot"].as_str() {
                        names.insert(id.to_owned(), slot["name"].clone());
                    }
                }
            }
        }
        for key in schema.slots.keys() {
            names.entry(key.clone()).or_insert(json!(key));
        }
        let source = schema.provenance["source_id"].clone();
        let parent = source
            .as_str()
            .and_then(|id| state["binder_sources"].get(id))
            .map(|s| s["parent_source_id"].clone())
            .unwrap_or(Value::Null);
        let mut dependencies = Vec::new();
        if let Some(witnesses) = schema.provenance["lowered"]["witnesses"].as_array() {
            for witness in witnesses.iter().filter_map(Value::as_str) {
                let id = format!("witness_function:{witness}");
                let declaration = state["declarations"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter_map(Value::as_str)
                    .find(|d| {
                        d.starts_with(&format!("(declare-fun {witness} "))
                            || d.starts_with(&format!("(define-fun {witness} "))
                    })
                    .unwrap_or(witness);
                records.insert(id.clone(),json!({"id":id,"kind":"source","expression":declaration,"sort":null,"frame":null,"links":{},"data":{"source_kind":"definition","parent_ref":source}}));
                dependencies.push(id);
            }
        }

        records.insert(schema.id.clone(), json!({"id":schema.id,"kind":"schema","expression":schema.formula,"sort":"Bool","frame":null,"links":{},"data":{"slots":schema.slots,"slot_names":names,"direction":schema.provenance["direction"].as_str().unwrap_or("array_axiom"),"source_ref":source,"parent_ref":parent,"witness_dependencies":dependencies}}));
    }
    records
}

pub(super) fn usage(checks: u64) -> Value {
    json!({"elapsed_ms":0,"expansion_work":0,"search_operations":0,"solver_checks":checks,"solver_statistics":null})
}

fn term_frame(term: &smt2parser::concrete::Term) -> Option<u16> {
    fn collect(term: &smt2parser::concrete::Term, frames: &mut std::collections::BTreeSet<u16>) {
        use smt2parser::concrete::Term;
        match term {
            Term::QualIdentifier(id) => {
                if let Some((_, frame)) = smt2parser::vmt::split_framed_symbol(&id.get_name()) {
                    if let Ok(frame) = u16::try_from(frame) {
                        frames.insert(frame);
                    }
                }
            }
            Term::Application { arguments, .. } => {
                for argument in arguments {
                    collect(argument, frames);
                }
            }
            _ => {}
        }
    }
    let mut frames = std::collections::BTreeSet::new();
    collect(term, &mut frames);
    if frames.len() == 1 {
        frames.into_iter().next()
    } else {
        None
    }
}
