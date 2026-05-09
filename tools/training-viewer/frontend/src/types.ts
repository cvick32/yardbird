export interface BenchmarkSummary {
  name: string;
  run_count: number;
  latest_run: string;
  success_count: number;
  failure_count: number;
  cost_functions: string[];
}

export interface RunSummary {
  id: number;
  cost_function: string;
  success: boolean | null;
  total_refinements: number | null;
  total_time_ms: number | null;
  created_at: string;
  decision_count: number;
  abstract_count: number;
  indexed_count: number;
  core_pct: number | null;
}

export interface RunDetail {
  benchmark: {
    id: number;
    name: string;
    cost_function: string;
    success: boolean | null;
    total_refinements: number | null;
    total_time_ms: number | null;
    created_at: string;
  };
  counts: {
    decision_count: number;
    candidate_count: number;
    abstract_count: number;
    abstract_core_count: number;
    indexed_count: number;
    indexed_core_count: number;
    core_appearance_count: number;
  };
}

export interface Decision {
  id: number;
  decision_key: string | null;
  bmc_depth: number;
  axiom_name: string;
  slot_index: number;
  created_at: string;
  candidate_count: number;
  chosen_count: number;
  has_bad_decision_shape: boolean;
}

export interface Candidate {
  id: number;
  term: string;
  decision_id: number;
  term_hash: string;
  is_constant: boolean;
  is_variable: boolean;
  in_property_vocab: boolean;
  in_transition_vocab: boolean;
  frame_index: number | null;
  ast_size: number;
  current_cost: number;
  was_chosen: boolean;
}

export interface AbstractInstantiation {
  id: number;
  benchmark_id: number;
  abstract_instantiation_id: string;
  term: string;
  term_hash: string;
  axiom_name: string;
  bmc_depth: number;
  refinement_step: number;
  in_unsat_core: boolean;
  decision_link_count: number;
}

export interface IndexedInstantiation {
  id: number;
  benchmark_id: number;
  label: string;
  term: string;
  term_hash: string;
  depth: number;
  unroll_index: number;
  abstract_instantiation_db_id: number | null;
  abstract_instantiation_id: string | null;
  in_unsat_core: boolean;
  has_abstract_link: boolean;
}

export interface ProvenanceRow {
  decision_id: number;
  axiom_name: string;
  decision_depth: number;
  slot_index: number;
  abstract_id: number;
  abstract_term: string;
  abstract_in_core: boolean;
  abstract_axiom: string;
  abstract_depth: number;
  refinement_step: number;
  indexed_id: number | null;
  indexed_term: string | null;
  indexed_in_core: boolean | null;
  indexed_depth: number | null;
  indexed_label: string | null;
}
