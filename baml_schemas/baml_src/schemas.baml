// BAML schemas for Yardbird verification assistance

// Input context for invariant generation
class VerificationContext {
  // Program variables and their types
  variables string[]
  
  // Initial conditions from the VMT file
  init_conditions string
  
  // Transition conditions (loop body)
  trans_conditions string
  
  // Target property to prove
  property string
  
  // Array operations detected in the program
  array_operations string[]
  
  // Loop bounds or constraints
  loop_bounds string[]
  
  // Additional context or hints
  hints string[]
}

// Response with single best invariant suggestion
class InvariantSuggestions {
  // Single best candidate invariant
  candidate_formula string
  
  // General analysis of the verification task
  analysis string
  
  // Suggested verification strategy
  strategy_hints string[]
}

// Specific analysis request types
enum AnalysisType {
  PROPOSE_INVARIANT
  ANALYZE_COUNTEREXAMPLE
  SUGGEST_LEMMAS
  DEBUG_STRATEGY
}

// Request for verification assistance
class VerificationRequest {
  analysis_type AnalysisType
  context VerificationContext
  
  // Optional: previous failed attempts
  failed_invariants string[]
  
  // Optional: counterexample information
  counterexample string?
  
  // Optional: current proof strategy being used
  current_strategy string?
}