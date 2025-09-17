// BAML functions for invariant generation and verification assistance

function ProposeInvariant(request: VerificationRequest) -> InvariantSuggestions {
  client GPT4
  prompt #"
    You are an expert in formal verification and loop invariant generation. 
    You specialize in analyzing array manipulation programs and generating 
    inductive invariants for bounded model checking.
    
    ## Context
    Variables: {{ request.context.variables }}
    Initial conditions: {{ request.context.init_conditions }}
    Transition conditions: {{ request.context.trans_conditions }}
    Property to prove: {{ request.context.property }}
    Array operations: {{ request.context.array_operations }}
    Loop bounds: {{ request.context.loop_bounds }}
    
    {% if request.failed_invariants %}
    ## Previous Failed Attempts
    {% for failed in request.failed_invariants %}
    - {{ failed }}
    {% endfor %}
    {% endif %}
    
    {% if request.counterexample %}
    ## Counterexample Information
    {{ request.counterexample }}
    {% endif %}
    
    ## Task
    Generate 3-5 candidate loop invariants that could help prove the given property.
    Focus on:
    1. Array bounds and index relationships
    2. Array content preservation or transformation
    3. Loop counter relationships
    4. Relationships between different arrays
    
    For each invariant:
    - Provide the formula in SMT-LIB format
    - Explain why it should be inductive
    - Rate confidence (0-100)
    - Identify the type of invariant
    
    ## Output Format
    Return a structured response with multiple invariant candidates, analysis, and strategy hints.
    
    ## Example Invariant Types
    - Array bounds: (and (>= i 0) (<= i n))
    - Array content: (forall ((j Int)) (=> (and (>= j 0) (< j i)) (= (select a j) (select b j))))
    - Loop relationship: (= (+ i0 iterations) i)
    
    Be precise with SMT-LIB syntax and ensure invariants are likely to be inductive.
  "#
}

function AnalyzeCounterexample(request: VerificationRequest) -> InvariantSuggestions {
  client GPT4
  prompt #"
    You are analyzing a counterexample from a failed verification attempt.
    
    ## Context
    Variables: {{ request.context.variables }}
    Property: {{ request.context.property }}
    
    ## Counterexample
    {{ request.counterexample }}
    
    ## Failed Invariants
    {% for failed in request.failed_invariants %}
    - {{ failed }}
    {% endfor %}
    
    ## Task
    Analyze why the verification failed and suggest:
    1. Stronger invariants that would exclude this counterexample
    2. Additional lemmas that might be needed
    3. Whether the property itself is incorrect
    
    Focus on understanding the root cause of the failure and proposing
    specific fixes rather than general suggestions.
  "#
}

function SuggestLemmas(request: VerificationRequest) -> InvariantSuggestions {
  client GPT4
  prompt #"
    You are suggesting auxiliary lemmas for a verification task.
    
    ## Context
    Variables: {{ request.context.variables }}
    Initial conditions: {{ request.context.init_conditions }}
    Transition conditions: {{ request.context.trans_conditions }}
    Property: {{ request.context.property }}
    
    ## Current Strategy
    {{ request.current_strategy }}
    
    ## Task
    Suggest auxiliary lemmas that could help the verification succeed.
    These might include:
    1. Array axiom instantiations
    2. Arithmetic relationships
    3. Intermediate properties that build toward the main goal
    
    Focus on lemmas that are likely to be useful for automated theorem provers.
  "#
}