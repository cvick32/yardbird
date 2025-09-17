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

// Generated invariant candidate
class InvariantCandidate {
  // The invariant formula in SMT-LIB format
  formula string
  
  // Confidence score (0-100)
  confidence int
  
  // Explanation of why this invariant should hold
  reasoning string
  
  // Variables referenced in the invariant
  referenced_vars string[]
  
  // Type of invariant (e.g., "array_bounds", "loop_counter", "array_content")
  invariant_type string
}

// Response with multiple invariant suggestions
class InvariantSuggestions {
  // List of candidate invariants
  candidates InvariantCandidate[]
  
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