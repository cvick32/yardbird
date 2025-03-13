use std::collections::HashSet;

use smt2parser::{
    concrete::Term,
    vmt::{bmc::BMCBuilder, non_boolean_subterms::NonBooleanSubterms, ReadsAndWrites},
};

#[derive(Debug)]
pub struct SubtermHandler {
    initial_term: Term,
    trans_term: Term,
    prop_term: Term,
    initial_subterms: HashSet<Term>,
    trans_subterms: HashSet<Term>,
    prop_subterms: HashSet<Term>,
    instantiation_subterms: HashSet<Term>,
    initial_reads_and_writes: ReadsAndWrites,
    trans_reads_and_writes: ReadsAndWrites,
    prop_reads_and_writes: ReadsAndWrites,
    instantiation_reads_and_writes: ReadsAndWrites,
    init_and_trans_asserts: Vec<String>,
    prop_assert: String,
}

impl SubtermHandler {
    pub(crate) fn new(initial_term: Term, trans_term: Term, prop_term: Term) -> Self {
        SubtermHandler {
            initial_term,
            trans_term,
            prop_term,
            initial_subterms: HashSet::new(),
            trans_subterms: HashSet::new(),
            prop_subterms: HashSet::new(),
            instantiation_subterms: HashSet::new(),
            initial_reads_and_writes: ReadsAndWrites::default(),
            trans_reads_and_writes: ReadsAndWrites::default(),
            prop_reads_and_writes: ReadsAndWrites::default(),
            instantiation_reads_and_writes: ReadsAndWrites::default(),
            init_and_trans_asserts: vec![],
            prop_assert: "".into(),
        }
    }

    pub(crate) fn get_all_subterms(&self) -> Vec<&Term> {
        self.initial_subterms
            .iter()
            .chain(
                self.trans_subterms.iter().chain(
                    self.prop_subterms
                        .iter()
                        .chain(self.instantiation_subterms.iter()),
                ),
            )
            .collect()
    }

    pub(crate) fn register_instantiation_term(&mut self, inst: Term) {
        let mut inst_subterms = NonBooleanSubterms::default();
        let _ = inst.clone().accept_term_visitor(&mut inst_subterms);
        let _ = inst
            .clone()
            .accept_term_visitor(&mut self.instantiation_reads_and_writes);
        self.instantiation_subterms.extend(inst_subterms.subterms);
    }

    pub(crate) fn generate_subterms(&mut self, bmc_builder: &mut BMCBuilder) {
        // Only build initial subterms once.
        if bmc_builder.depth == 0 {
            let mut initial_subterms = NonBooleanSubterms::default();
            let indexed_initial_term = self.initial_term.clone().accept(bmc_builder).unwrap();
            self.init_and_trans_asserts
                .push(indexed_initial_term.to_string());
            let _ = indexed_initial_term
                .clone()
                .accept_term_visitor(&mut initial_subterms);
            let _ = indexed_initial_term
                .clone()
                .accept_term_visitor(&mut self.initial_reads_and_writes);
            self.initial_subterms = initial_subterms.subterms;
        } else {
            // Have to set backwards so we get 0->1 for depth 1.
            let cur_depth = bmc_builder.depth;
            bmc_builder.set_depth(cur_depth - 1);
            let mut trans_subterms = NonBooleanSubterms::default();
            let indexed_trans_term = self.trans_term.clone().accept(bmc_builder).unwrap();
            // Reset the depth.
            bmc_builder.set_depth(cur_depth);
            self.init_and_trans_asserts
                .push(indexed_trans_term.clone().to_string());
            let _ = indexed_trans_term
                .clone()
                .accept_term_visitor(&mut trans_subterms);
            self.trans_subterms.extend(trans_subterms.subterms);
            // Union up all of the trans subterms.
            let _ = indexed_trans_term
                .clone()
                .accept_term_visitor(&mut self.trans_reads_and_writes);
        }
        // Fully replace prop subterms every iteration.
        let mut prop_subterms = NonBooleanSubterms::default();
        self.prop_reads_and_writes = ReadsAndWrites::default();
        let indexed_prop_term = self.prop_term.clone().accept(bmc_builder).unwrap();
        self.prop_assert = indexed_prop_term.clone().to_string();
        let _ = indexed_prop_term
            .clone()
            .accept_term_visitor(&mut prop_subterms);
        let _ = indexed_prop_term
            .clone()
            .accept_term_visitor(&mut self.prop_reads_and_writes);
        self.prop_subterms = prop_subterms.subterms;
    }

    pub fn get_reads_and_writes(&self) -> ReadsAndWrites {
        let mut all_reads_from = HashSet::new();
        all_reads_from.extend(self.initial_reads_and_writes.reads_from.clone());
        all_reads_from.extend(self.trans_reads_and_writes.reads_from.clone());
        all_reads_from.extend(self.prop_reads_and_writes.reads_from.clone());
        all_reads_from.extend(self.instantiation_reads_and_writes.reads_from.clone());

        let mut all_writes_to = HashSet::new();
        all_writes_to.extend(self.initial_reads_and_writes.writes_to.clone());
        all_writes_to.extend(self.trans_reads_and_writes.writes_to.clone());
        all_writes_to.extend(self.prop_reads_and_writes.writes_to.clone());
        all_writes_to.extend(self.instantiation_reads_and_writes.writes_to.clone());

        ReadsAndWrites::from(all_reads_from, all_writes_to)
    }

    pub(crate) fn get_initial_subterms(&self) -> Vec<String> {
        self.initial_subterms
            .iter()
            .map(|ts| ts.to_string())
            .collect()
    }

    pub(crate) fn get_transition_system_subterms(&self) -> Vec<String> {
        self.trans_subterms
            .iter()
            .map(|ts| ts.to_string())
            .collect()
    }

    pub(crate) fn get_instantiation_subterms(&self) -> Vec<String> {
        self.instantiation_subterms
            .iter()
            .map(|ts| ts.to_string())
            .collect()
    }

    pub(crate) fn get_property_subterms(&self) -> Vec<String> {
        self.prop_subterms.iter().map(|ts| ts.to_string()).collect()
    }

    pub(crate) fn get_property_assert(&self) -> Term {
        self.prop_assert.parse().unwrap()
    }
}
