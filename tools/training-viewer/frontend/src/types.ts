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

export type TrainingDatabaseId = "local" | "lab";

export interface TrainingDatabaseOption {
  id: TrainingDatabaseId;
  label: string;
  configured: boolean;
}

export type EvalEnvironment = "local" | "aws" | "lab";
export type EvalStatus = "RUNNING" | "COMPLETED" | "FAILED";

export interface EvalRunIndexEntry {
  run_id: string;
  name: string | null;
  env: EvalEnvironment;
  status: EvalStatus;
  started_at: string;
  updated_at: string;
  benchmark_types: string[];
  manifest_path: string;
}

export interface EvalRunsIndex {
  runs: EvalRunIndexEntry[];
}

export interface EvalSubrun {
  benchmark_type: string;
  status: EvalStatus;
  started_at: string;
  completed_at: string | null;
  mode: EvalEnvironment;
  worker_vmid?: number;
  worker_node?: string;
  worker_name?: string;
  worker_ip?: string | null;
  worker_destroyed_at?: string;
  keep_vm?: boolean;
  cleanup_pending?: boolean;
  cleanup_error?: string;
  last_observed_vm_state?: string;
  last_checked_at?: string;
  r2_bucket?: string;
  r2_prefix?: string;
  r2_results_key?: string;
  r2_completion_key?: string;
  r2_failure_key?: string;
  result_path?: string;
  download_dir?: string;
  error?: string;
}

export interface EvalRunManifest {
  run_id: string;
  name: string;
  env: EvalEnvironment;
  status: EvalStatus;
  started_at: string;
  updated_at: string;
  completed_at: string | null;
  benchmark_types: string[];
  config_path: string;
  run_dir: string;
  manifest_path: string;
  progress: {
    completed: number;
    failed: number;
    running: number;
    total: number;
  };
  report: null | Record<string, unknown>;
  subruns: EvalSubrun[];
  training_enabled?: boolean;
  training_version?: string | null;
  postgres_sidecar?: unknown;
  lab?: Record<string, unknown>;
}

export interface LaunchEvalRunRequest {
  env: EvalEnvironment;
  benchmarkTypes: string[];
  name?: string;
  config?: string;
  lab?: {
    proxmoxInsecure?: boolean;
    workerTemplate?: string;
    workerUser?: string;
    workerSshKey?: string;
    r2Prefix?: string;
    keepVms?: boolean;
  };
}

export interface EvalRunActionResult {
  command: {
    stdout: string;
    stderr: string;
  };
  manifest?: EvalRunManifest;
  index?: EvalRunsIndex;
}
