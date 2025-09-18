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
    Generate the single best loop invariant that you are most confident would help prove the given property.
    Focus on the most critical relationship needed for the proof.
    
    Return only:
    - The invariant formula in SMT-LIB format.
    
    ## Output Format
    Return a JSON object with this exact structure:
    {
      "candidate_formula": "your_invariant_formula_here"
    }
    
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
    Analyze why the verification failed and suggest the single best strengthened invariant 
    that would exclude this counterexample.
    
    ## Output Format
    Return a JSON object with this exact structure:
    {
      "candidate_formula": "your_strengthened_invariant_here"
    }
    
    Focus on understanding the root cause and providing a precise SMT-LIB formula.
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
    Suggest the single most important auxiliary lemma that could help the verification succeed.
    
    ## Output Format
    Return a JSON object with this exact structure:
    {
      "candidate_formula": "your_lemma_formula_here"
    }
    
    Focus on lemmas that are likely to be useful for automated theorem provers.
    Provide the lemma in precise SMT-LIB syntax.
  "#
}

function ClassifyCounterexample(request: VerificationRequest) -> CounterexampleClassification {
  client GPT4

  prompt #"
    You are an SMT-savvy assistant helping with program verification. 
    Your job: classify the supplied counterexample as a brief conjunction of predicates in the *quantifier-free theory of integers with equality and linear arithmetic* (no arrays, no user-defined functions, no disjunctions, no quantifiers). Then provide a very short natural-language explanation.

    ### Output format (STRICT)
    Return **only** valid JSON matching:
    {{
      "conjuncts": ["<predicate>", "..."],
      "explanation": "<short sentence>"
    }}

    No extra fields, prose, or code fences.

    ### Predicate language (STRICT)
    - Allowed atomic forms over integer variables from `Variables`:
      - Equality / disequality: `x = t`, `x != t`
      - Inequalities: `x <= t`, `x < t`, `x >= t`, `x > t`
    - Terms `t` must be *linear integer terms*: `c`, `x`, `x + c`, `x - c`, `x + y`, `x - y`, `c1*x + c2*y + c3` with integer coefficients. 
    - **No multiplication between variables** (i.e., at most constant × variable). Prefer normalized linear forms (e.g., `2*i - n <= 0`).
    - Use only variables listed in `Variables`. Do **not** invent new symbols or arrays.
    - Conjunction only (an array of predicates). **No ORs**, **no →**, **no quantifiers**, **no function symbols**.
    - Keep predicates **minimal but sufficient** to characterize why the property fails on this trace (e.g., a threshold relation, a sign/ordering relation, a simple affine relation).

    ### How to think (keep this reasoning internal; do not print it)
    1) Parse the initial, transition, and property constraints. If `counterexample` is given, use it to infer critical linear relations observed along the failing path.
    2) Generalize the failure cause to a small set of linear predicates that explain the violation (e.g., “loop runs long enough that acc drops below 0” → `acc < 0 ∧ i >= 1`).
    3) Prefer simplest normalized linear relations that are stable across steps (thresholds, monotone bounds, off-by-one relations).
    4) If context is insufficient, return `conjuncts: []` and a brief explanation like `"insufficient context"`.

    ### Style
    - Keep `explanation` to a single short sentence (<= 20 words).
    - Normalize whitespace (e.g., `i <= n - 1`), keep all variables and integers lowercase/plain.

    ### Context
    Variables: {{ request.context.variables }}
    Initial conditions: {{ request.context.init_conditions }}
    Transition conditions: {{ request.context.trans_conditions }}
    Property: {{ request.context.property }}
    Counterexample (optional): {{ request.counterexample }}

    ### Examples

    # Example A
    # Vars: ["i:int","n:int","acc:int"]
    # Init: "i = 0 ∧ acc = 0"
    # Trans: "i' = i + 1 ∧ acc' = acc - 5"
    # Prop:  "acc >= 0"
    # CEX:   "step0: i=0,acc=0; step1: i=1,acc=-5"
    Expected JSON:
    {{
      "conjuncts": ["acc < 0", "i >= 1"],
      "explanation": "acc decreases each step; after one step it violates nonnegativity."
    }}

    # Example B
    # Vars: ["i:int","n:int"]
    # Init: "i = 0"
    # Trans: "i' = i + 2"
    # Prop:  "i <= n"
    # CEX:   "n = 0; step1: i=2"
    Expected JSON:
    {{
      "conjuncts": ["i > n", "i >= 2", "n = 0"],
      "explanation": "i grows by two and quickly exceeds the fixed bound n."
    }}
"#
}
