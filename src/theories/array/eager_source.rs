//! Original-input vocabulary for eager ablations, captured before strategy rewrites.
use smt2parser::{
    concrete::{Command, Term},
    vmt::{
        bmc::BMCBuilder, definition_graph::DefinitionFrameInfo,
        definition_materializer::DefinitionMaterializer, VMTModel,
    },
};

use crate::smtlib_problem::SMTLIBProblem;
use crate::{
    instance_installation::request::InstantiationRequest,
    rule_matching::provenance::InstantiationProvenance,
};

pub(crate) struct SourceVocabulary {
    pub declarations: Vec<Command>,
    pub array_types: Vec<(String, String)>,
    pub initial_and_transition: Vec<Term>,
    pub property: Vec<Term>,
}

pub(crate) struct EagerSource {
    pub vocabulary: SourceVocabulary,
    frames: DefinitionFrameInfo,
}

impl EagerSource {
    pub(crate) fn vmt(model: &VMTModel) -> Self {
        let current = model.get_all_current_variable_names();
        let next = model.get_next_to_current_varible_names();
        let definitions = model.get_helper_definitions().clone();
        let frames = DefinitionFrameInfo::new(&definitions, &current, &next);
        let mut builder = BMCBuilder::with_definition_frames(current, next, frames.clone());
        let mut definitions = DefinitionMaterializer::new(definitions, frames.clone());
        let mut with_support = |term: Term| {
            let root = builder.index_single_step_term(term);
            let materialized = definitions.materialize(root, &mut builder);
            let mut terms = materialized.support;
            terms.push(materialized.root);
            terms
        };
        // Scan the whole source once. Current/next references become frames 0/1;
        // installation retains wider schemas until their frames are available.
        let initial_and_transition = [
            model.get_initial_condition_for_yardbird(),
            model.get_trans_condition_for_yardbird(),
        ]
        .into_iter()
        .chain(model.get_axioms())
        .flat_map(&mut with_support)
        .collect();
        let property = with_support(model.get_property_for_yardbird());
        Self {
            vocabulary: SourceVocabulary {
                declarations: model.as_commands(),
                array_types: model.abstract_array_theory().1,
                initial_and_transition,
                property,
            },
            frames,
        }
    }

    pub(crate) fn smtlib(problem: &SMTLIBProblem) -> Self {
        Self {
            vocabulary: SourceVocabulary {
                declarations: problem.as_commands(),
                array_types: problem.abstract_array_theory().1,
                initial_and_transition: vec![],
                property: problem.get_assertion_terms(),
            },
            frames: DefinitionFrameInfo::default(),
        }
    }

    pub(crate) fn make_request(
        &self,
        term: Term,
        provenance: InstantiationProvenance,
    ) -> Option<InstantiationRequest> {
        let (id, substitution) = provenance.into_parts();
        let (instance, substitution) =
            smt2parser::vmt::UnquantifiedInstantiator::rewrite_with_definitions_and_substitution(
                term,
                self.frames.clone(),
                substitution,
            )?;
        Some(
            InstantiationRequest::provenanced(
                instance,
                InstantiationProvenance::new(id, substitution),
            )
            .with_replay_on_loop(),
        )
    }
}
