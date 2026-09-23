# Yardbird Agent Reference

A CEGAR (Counter-Example Guided Abstraction Refinement) tool for automated verification of array-manipulating programs. Yardbird performs bounded model checking on VMT (Verification Modulo Theories) and SMT-LIB format problems, using e-graph-based abstraction refinement with pluggable cost functions.

---

## Repository Layout

```
yardbird/                       # Root workspace
  src/                          # Main yardbird binary + library
    main.rs                     # Entry point: mode dispatch (VMT vs SMTLIB)
    lib.rs                      # Library root, CLI options, strategy builders
    driver.rs                   # CEGAR loop orchestrator (check_strategy)
    vmt_bmc_session.rs          # VMT temporal system solver (BMC unrolling)
    smtlib_problem.rs           # SMTLIB problem parser + simple solver
    smtlib_refinement_session.rs # Adapter: SMTLIB -> ProblemContext
    problem_context.rs         # Trait unifying SMT/SMTLIB problem access
    theory_support.rs           # TheorySupport trait + Array/List impls
    z3_var_context.rs           # SMT term -> Z3 AST conversion
    z3_ext.rs                   # Z3 model dumping utilities
    subterm_handler.rs          # Non-boolean subterm extraction
    proof_tree.rs               # Proof trace tracking
    interpolant.rs              # SMTInterpol wrapper
    ic3ia.rs                    # IC3IA algorithm invocation
    egg_utils.rs                # E-graph utility helpers
    problem.rs                  # Problem trait (get_sorts, check, unroll)
    logger.rs                   # env_logger init
    utils.rs                    # SolverStatistics, general utils
    strategies/
      abstract.rs               # Shared coordinator + RefinementState
      array_abstract_with_quantifiers.rs  # Quantified-axiom solver variant
      array_concrete.rs         # ConcreteArrayZ3
      list_abstract.rs          # ListAbstract
      proof_strategy.rs         # ProofStrategy + ProofStrategyExt
      interpolate.rs, repl.rs   # Strategy extensions
    terms/
      language.rs               # TermLanguage, TermExpr, TermPattern, SMT conversion
      preprocess.rs             # Typed operator preprocessing for e-graph syntax
    rule_matching/
      search_context.rs         # Borrowed graph, policy, and history inputs
      compiled_rule.rs          # Shared executable rule representation
      search.rs                 # Match enumeration and search reports
      extractor.rs              # Shared representative extraction
      grounding.rs              # Substitutions and shared grounding primitives
      candidate_builder.rs      # Match-to-candidate construction
      candidate.rs              # Candidate data and model validation
      rule.rs, provenance.rs    # Shared identities and candidate provenance
      scope.rs                  # Candidate eligibility scope
    theories/
      array/
        refinement.rs           # Array abstraction, encodings, and candidate batches
        array_axioms.rs         # Built-in array axioms
        search.rs               # Array backoff search using policy allowances
        grounding.rs            # Read/write structure and source-write alternatives
        term_index.rs           # Source-write indexes and model-local lookup caches
        rule.rs, candidate.rs   # Array rule kinds and synthesis observations
        transition_guard.rs     # Array-read guard recognition
        array_egraph_builder.rs # Staged array vocabulary admission
        array_dataflow.rs       # Property cone analysis
        encodings/              # Array preprocessing and abstraction encodings
      quantifiers/
        mod.rs, lowering.rs     # Binder plans and closure conversion
        refinement.rs           # Quantifier refinement over the shared graph
        compiled_rule.rs        # Binder compilation and violation-filter metadata
        search.rs               # Binder paging and continuation cursors
        binder_request.rs       # Directed requests and bindings
        dependency_search.rs    # Dependency paths
        violation_plan.rs       # Signed violation plans
        provenance.rs, rule.rs  # Source provenance and binder identity
        transition_guard.rs     # Quantified transition conditions and substitution
      list/, bvlist/            # Existing theory implementations
    policy.rs                   # YardbirdPolicy composition and named policies
    policy/
      effort.rs                 # Search scheduling and work allowances
      instance_selection.rs     # Whole-instance ranking and batch selection
      term_selection/
        mod.rs                  # YardbirdCostFunction and TermCostFactory
        context.rs              # TermCostContext
        array/                  # Array-specific scoring heuristics
        list/, bvlist/          # Existing cost implementations
    instance_installation/
      mod.rs                    # Installation mechanics and replay strategy interface
      request.rs, provenance.rs # Requests, outcomes, and absolute-frame substitutions
      assertion_tracker.rs      # Assertion identity and deduplication
      full_unroll.rs, no_unroll_on_loop.rs, schema_batch.rs
    refinement_graph.rs         # One coordinator-owned model-equivalence graph
    refinement_graph/           # Shared vocabulary growth
    profiling.rs                # RefinementProfilingCollector and solver observations
    training/                   # Trajectories, learning, and persistence
  smt2parser/                   # SMT-LIB 2 parser (workspace member)
    src/
      lib.rs                    # Parser exports
      main.rs                   # smt2bin CLI
      lexer.rs                  # Tokenizer
      parser.rs                 # Grammar
      concrete.rs               # AST types (Term, Command, Sort, etc.)
      visitors.rs               # Visitor pattern + Identifier types
      renaming.rs               # Symbol normalization
      rewriter.rs               # Term rewriting framework
      constant_abstraction.rs   # Constant abstraction pass
      let_extract.rs            # Let-binding extraction
      stats.rs                  # Counter statistics
      vmt/
        mod.rs                  # VMTModel struct + parser
        variable.rs             # State variable (current/next pair)
        action.rs               # Transition actions
        axiom.rs                # Model axioms
        bmc.rs                  # BMCBuilder - time-step indexing
        smt.rs                  # SMT integration
        array_abstractor.rs     # select/store -> Read/Write conversion
        array_axiom_frame_num_getter.rs
        quantified_instantiator.rs   # Instance struct, quantifier handling
        reads_and_write.rs      # ReadsAndWrites metadata
        non_boolean_subterms.rs # Subterm visitor
        numbered_to_symbolic.rs
        canonicalize_boolean.rs
        smtinterpol_utils.rs
        utils.rs
  garden/                       # Benchmark runner
  coop/                         # Proof-of-concept examples with #[ensures]
  to_vmt/                       # VMT code gen from Rust annotations
    vmt_macros/                 # #[ensures(...)] proc macro
    vmtil/                      # VMT Intermediate Language
  examples/
    array/                      # ~191 VMT array benchmarks
    list/                       # 11 list theory examples
    bvlist/                     # 6 bitvector list examples
    smt2/                       # 6 SMTLIB examples
    smtlib/                     # 6 additional SMTLIB examples
    two_dimensional_array/      # 8 2D array examples
  tests/
    snapshot_tests.rs           # Insta snapshot tests
  benchmark_results/            # Stored benchmark JSON results
```

### Ownership rules

`rule_matching` contains machinery shared by array axioms and general quantifiers.
Theory-specific preparation and semantics belong under the corresponding theory.
Policy controls effort and preferences; validation remains separate. The abstract
coordinator owns graph mutation and model/history lifetimes, passing borrowed
`SearchContext` to theory searches. Installation owns BMC placement and replay.
Keep one shared graph and retain observation links across these modules.

---

## Execution Flow

### CLI Options (`src/lib.rs`)

```
yardbird --filename <file> [options]

Required:
  -f, --filename <FILE>      Input .vmt or .smt2 file

Key options:
  -d, --depth <N>            BMC depth (default: 10)
  -s, --strategy <STR>       abstract | abstract-with-quantifiers | concrete
  -c, --cost-function <CF>   bmc-cost | ast-size | adaptive-cost | split-cost |
                             prefer-read | prefer-write | prefer-constants
  -t, --theory <TH>          array | list | bv-list
  --instantiation-strategy   full-unroll | no-unroll-on-loop
  --json-output              JSON output for garden integration
  --run-ic3ia                Run IC3IA after BMC
  --interpolate              Use SMTInterpol
  --abstract-recurrent-products       Abstract eligible nonlinear products
  --repl                     Interactive mode
  --dump-solver <PATH>       Dump Z3 state on unsat
  --track-instantiations     Enable unsat core tracking
  --dump-unsat-core <PATH>   Export unsat core JSON
```

### Mode Dispatch (`src/main.rs`)

```
main()
  ├─ .smt2 extension -> run_smtlib_mode()
  │   ├─ Simple mode (Concrete + BmcCost) -> SmtlibCommandExecutor::execute()
  │   └─ Strategy mode -> SmtlibRefinementRunner::execute()
  └─ .vmt extension -> run_vmt_mode()
      ├─ Theory::Array  -> build_array_proof_plan(); check plan.strategy
      ├─ Theory::List   -> Driver::check_strategy(build_list_strategy())
      └─ Theory::BvList -> todo!()
```

### CEGAR Loop (`src/driver.rs`)

```
check_strategy(target_depth, strategy):
  model = strategy.configure_model(model)    // abstract array ops
  smt_problem = VmtBmcSession::new(model, strategy)
  for depth in 0..target_depth:              // outer BMC loop
    for refinement_step in 0..strategy.refinement_limit().unwrap_or(u32::MAX):
      smt_problem.unroll(depth)
      state = strategy.setup(smt, depth)
      match smt_problem.check():
        Unsat   -> strategy.unsat()   -> NextDepth
        Sat     -> strategy.sat()     -> Continue (refine) or FoundCounterexample
        Unknown -> strategy.unknown() -> error
      match action:
        Continue            -> extensions.refine(...), then strategy.finish(...)
        NextDepth           -> continue to next depth
        FoundCounterexample -> return error
        FoundProof          -> return result
    TooManyRefinements error if inner loop exhausted
```

---

## Core Traits

### ProofStrategy (`src/strategies/proof_strategy.rs`)

```rust
pub trait ProofStrategy<'ctx, S> {
    fn get_theory_support(&self) -> Box<dyn TheorySupport>;
    fn configure_model(&mut self, model: VMTModel) -> VMTModel;  // default: identity
    fn refinement_limit(&self) -> Option<u32>;                    // abstract: no fixed cap
    fn setup(&mut self, smt: &dyn ProblemContext, depth: u16) -> Result<S>;
    fn unsat(&mut self, state: &mut S, smt: &dyn ProblemContext) -> Result<ProofAction>;
    fn sat(&mut self, state: &mut S, smt: &dyn ProblemContext, step: u32) -> Result<ProofAction>;
    fn unknown(&mut self, state: &mut S, smt: &dyn ProblemContext) -> Result<ProofAction>;
    fn finish(&mut self, state: S, smt: &mut dyn ProblemContext) -> Result<()>;
    fn result(&mut self, model: &mut VMTModel, smt: &dyn ProblemContext) -> ProofLoopResult;
}
```

### ProblemContext (`src/problem_context.rs`)

The shared refinement interface exposes model evaluation, source and derived
subterms, array types, variables, installation requests, and solver statistics.
It is implemented by `VmtBmcSession` and `SmtlibRefinementSession`; concrete solver
backends live behind `YardbirdSolver` in `src/solver/`.

```rust
pub trait ProblemContext {
    fn has_model(&self) -> bool;
    fn eval_to_string(&self, term: &Term) -> anyhow::Result<String>;
    fn get_all_subterms(&self) -> Vec<&Term>;
    fn add_instantiation(&mut self, request: InstantiationRequest) -> InstantiationInstallResult;
    fn get_instantiations(&self) -> Vec<Term>;
    fn get_variables(&self) -> &[Variable];
    fn get_reads_and_writes(&self) -> ReadsAndWrites;
    fn get_array_types(&self) -> Vec<(String, String)>;
    fn get_solver_statistics(&self) -> SolverStatistics;
    fn get_reason_unknown(&self) -> Option<String>;
    // Additional source-vocabulary, auxiliary, and profiling operations.
}
```

### TheorySupport (`src/theory_support.rs`)

```rust
pub trait TheorySupport {
    fn get_uninterpreted_functions(&self) -> Vec<FunctionDeclaration>;
    fn get_axiom_formulas(&self) -> Vec<Command>;
    fn get_logic_string(&self) -> String;
    fn abstract_model(&self, model: VMTModel) -> (VMTModel, Vec<(String, String)>);
    fn requires_abstraction(&self) -> bool;
    fn uses_quantified_axioms(&self) -> bool;
}
```

Implementations:
- `ArrayTheorySupport` - uninterpreted Read/Write/ConstArr, no axioms, UFLIA/AUFBV logic
- `ArrayWithQuantifiersTheorySupport` - adds forall-quantified array axioms
- `ConcreteArrayTheory` - no abstraction, QF_AUFLIA logic
- `ListTheorySupport` - list operations

### YardbirdCostFunction (`src/policy/term_selection/mod.rs`)

```rust
pub trait YardbirdCostFunction<L>: egg::CostFunction<L, Cost = u32> + Clone
where L: egg::Language + egg::FromOp
{
    fn get_string_terms(&self) -> Vec<String>;
    fn get_reads_and_writes(&self) -> ReadsAndWrites;
    fn get_parsed_terms(&self) -> Vec<egg::RecExpr<L>>;
}
```

### InstantiationStrategy (`src/instance_installation/mod.rs`)

```rust
pub trait InstantiationStrategy: Debug + Send {
    fn clone_box(&self) -> Box<dyn InstantiationStrategy>;
    fn on_generate(&mut self, request: InstantiationRequest, context: &mut InstantiationContext) -> InstantiationInstallResult;
    fn on_loop(&mut self, depth: u16, context: &mut InstantiationContext);
}
```

---

## Array Theory (Primary Focus)

### Array Abstraction Pipeline

```
1. Input VMT/SMTLIB with native array ops (select, store, const)
       |
2. ArrayAbstractor (smt2parser/src/vmt/array_abstractor.rs)
   - Converts:  (select A i) -> (Read_Int_Int A i)
                (store A i v) -> (Write_Int_Int A i v)
                ((as const (Array Int Int)) v) -> (ConstArr_Int_Int v)
   - Converts sorts:  (Array Int Int) -> Array_Int_Int
   - Discovers type pairs: [(Int, Int), (BitVec32, Int), ...]
       |
3. TheorySupport registers uninterpreted function declarations for Z3
   - Read_I_V : (Array_I_V, I) -> V
   - Write_I_V : (Array_I_V, I, V) -> Array_I_V
   - ConstArr_I_V : (V) -> Array_I_V
       |
4. Z3 solver treats these as uninterpreted (no built-in array semantics)
       |
5. CEGAR refinement adds array axiom instances on demand
```

### TermLanguage (`src/terms/language.rs`)

E-graph language for array term manipulation (egg `define_language!`):

| Node | Arity | Description |
|------|-------|-------------|
| `ConstArr` (ConstArrTyped) | 3 | `[index_sort, value_sort, value]` |
| `Write` (WriteTyped) | 5 | `[index_sort, value_sort, array, index, value]` |
| `Read` (ReadTyped) | 4 | `[index_sort, value_sort, array, index]` |
| `and` | variadic | Boolean conjunction |
| `or` | variadic | Boolean disjunction |
| `not` | 1 | Boolean negation |
| `=>` | 2 | Implication |
| `=` | 2 | Equality |
| `>=`, `>`, `<=`, `<` | 2 | Comparisons |
| `+` | variadic | Addition |
| `-` | variadic | Subtraction/negation |
| `*` | variadic | Multiplication |
| `/`, `mod` | 2 | Division, modulo |
| `Symbol` | 0 | Variable/sort name |
| `Num` | 0 | Numeric literal |

Type aliases: `TermExpr = egg::RecExpr<TermLanguage>`, `TermPattern = egg::PatternAst<TermLanguage>`

### Array Axioms (Rewrite Rules)

Generated per type pair `(IndexSort, ValueSort)` in `array_axioms_for_type()`:

**1. write-does-not-overwrite** (conditional)
```
(Read IS VS (Write IS VS ?a ?idx ?val) ?c) => (Read IS VS ?a ?c)
  WHEN ?idx != ?c
```

**2. read-after-write**
```
(Read IS VS (Write IS VS ?a ?idx ?val) ?idx) => ?val
```

**3. constant-array**
```
(Read IS VS (ConstArr IS VS ?a) ?b) => ?a
```

### Refinement Cycle (Abstract Strategy)

`src/strategies/abstract.rs` implements `ProofStrategy<RefinementState>` and owns
one `RefinementGraph`. Array and quantifier refinement borrow this graph rather
than maintaining separate equality state.

1. Configure array abstraction and quantifier lowering in their theory modules.
2. Prepare a model-local graph and search state, preserving policy scheduling history.
3. Ask `policy/effort.rs` which operation to execute and with what allowance.
4. Enumerate matches through `rule_matching/search.rs`, using array backoff or
   quantifier paging from the corresponding theory module.
5. Build candidates through shared extraction and grounding, dispatching array
   structural handling to `theories/array/grounding.rs`.
6. Apply `policy/instance_selection.rs`, retaining term-selection observations.
7. Install selected instances through `instance_installation/`; grow vocabulary
   or allowances when more search is needed. Model equalities are never asserted
   as theory lemmas. A new solver model invalidates model-local matches and caches.

### Matching and extraction

`src/theories/array/array_axioms.rs` compiles the built-in rules. Shared matching
in `src/rule_matching/search.rs` is read-only. Binder-specific filters and paging
live under `src/theories/quantifiers/`.

`src/rule_matching/extractor.rs` builds ranked representative pools and delegates
preference to term-selection policies. `src/theories/array/term_index.rs` owns
source-write indexes and lookup caches. `src/rule_matching/candidate_builder.rs`
constructs complete candidates while preserving their provenance and decisions.

### Cost Functions (Array)

All in `src/policy/term_selection/array/`:

| Cost Function | File | Strategy |
|--------------|------|----------|
| BmcCost | `symbol_cost.rs` | Prefers terms from BMC structure (init/trans/prop subterms) |
| AstSize | `ast_size.rs` | Minimizes AST node count |
| AdaptiveCost | `adaptive_cost.rs` | Depth-aware penalties for nested array ops |
| SplitCost | `split_cost.rs` | Synthesizes critical index terms from property+transition patterns |
| PreferRead | `prefer_read.rs` | Biases toward Read operations |
| PreferWrite | `prefer_write.rs` | Biases toward Write operations |
| PreferConstants | `prefer_constants.rs` | Biases toward constant values |

---

## SMT Problem Handling

### VmtBmcSession (VMT Mode) (`src/vmt_bmc_session.rs`)

Represents a temporal transition system for BMC:

```rust
pub struct VmtBmcSession {
    bmc_builder: BMCBuilder,
    definition_materializer: DefinitionMaterializer,
    depth: u16,
    instantiations: Vec<StoredInstantiation>,
    subterm_handler: SubtermHandler,
    solver: Box<dyn YardbirdSolver>,
    instantiation_strategy: Box<dyn InstantiationStrategy>,
    assertion_tracker: InstantiationAssertionTracker,
    // Formulas, declarations, property activation, profiling, and tracking state.

}
```

Key operations:
- `new()` - creates solver, registers theory functions/axioms, asserts init condition
- `unroll(depth)` - adds time-step variables, asserts transition at depth, calls `on_loop`
- `check()` - push property negation, call Z3, capture model/proof, pop property
- `add_instantiation()` - adds instantiation via strategy's `on_generate` hook

### SMTLIBProblem (`src/smtlib_problem.rs`)

Parsed SMTLIB file:
- `from_path()` - stream-parses with `CommandStream`, applies let-extraction
- `abstract_array_theory()` - converts to uninterpreted functions
- `SmtlibCommandExecutor` - executes commands sequentially (assert, check-sat, push/pop)
- `SmtlibRefinementRunner` - drives strategy setup and refinement around a stateless SMT-LIB session

### Z3VarContext (`src/solver/z3_var_context.rs`)

Converts SMT2 parse tree to Z3 AST. Handles:
- Constants: numerals, hex (-> BV), true/false
- Applications: arithmetic, boolean, array (select/store/const), bitvector ops
- Quantifiers: forall with fresh variables + scope management
- Indexed operations: extract, zero_extend, sign_extend
- BV operations: bvadd, bvsub, bvmul, bvand, bvor, bvxor, bvnot, bvneg, shifts, comparisons

---

## Key Data Structures

### ProofLoopResult (`src/driver.rs`)

```rust
pub struct ProofLoopResult {
    pub model: Option<VMTModel>,           // instantiated VMT model
    pub used_instances: Vec<Term>,         // instantiations used in proof
    pub const_instances: Vec<Term>,        // high-cost constant instantiations
    pub solver_statistics: SolverStatistics,
    pub total_instantiations_added: u64,
    pub counterexample: bool,
    pub found_proof: bool,
}
```

### VMTModel (`smt2parser/src/vmt/mod.rs`)

```rust
pub struct VMTModel {
    sorts: Vec<Command>,                   // sort declarations
    state_variables: Vec<Variable>,        // current/next state var pairs
    function_definitions: Vec<Command>,    // function declarations
    actions: Vec<Action>,                  // transition actions
    _axioms: Vec<Axiom>,                   // domain axioms
    initial_condition: Term,               // I(x)
    transition_condition: Term,            // T(x, x')
    property_condition: Term,              // P(x)
}
```

### Variable (`smt2parser/src/vmt/variable.rs`)

```rust
pub struct Variable {
    pub current: Command,      // (declare-fun x () Sort)
    pub next: Command,         // (declare-fun x! () Sort)
    pub relationship: Command, // transition constraint
}
```

### RefinementState (`src/strategies/abstract.rs`)

```rust
pub struct RefinementState {
    pub depth: u16,
    pub egraph: RefinementGraph,
    pub candidates: Vec<InstantiationCandidate>,
    pub array_types: Vec<(String, String)>,
    // Model/graph versions, binder search caches, and staged array expansion.

}
```

### SubtermHandler (`src/subterm_handler.rs`)

```rust
pub struct SubtermHandler {
    initial_term: Term, trans_term: Term, prop_term: Term,
    initial_subterms: HashSet<Term>,
    trans_subterms: HashSet<Term>,
    prop_subterms: HashSet<Term>,
    instantiation_subterms: HashSet<Term>,
    initial_reads_and_writes: ReadsAndWrites,
    trans_reads_and_writes: ReadsAndWrites,
    prop_reads_and_writes: ReadsAndWrites,
    // ...
}
```

### Driver Errors (`src/driver.rs`)

```rust
pub enum Error {
    Counterexample,                           // real counterexample found
    NoProgress { depth, instantiations },     // refinement stalled
    TooManyRefinements { n_refines, depth },  // strategy-specific refinement limit
    Anyhow(anyhow::Error),                    // generic error
    SolverUnknown(Option<String>),            // Z3 returned unknown
    RecExpr(egg::RecExprParseError),          // e-graph parse failure
}
```

---

## Configuration Enums (`src/lib.rs`)

```rust
enum Strategy          { Abstract, AbstractWithQuantifiers, Concrete }
enum CostFunction      { BmcCost, AstSize, AdaptiveCost, SplitCost,
                         PreferRead, PreferWrite, PreferConstants }
enum Theory            { Array, BvList, List }
enum InstantiationStrategyType { FullUnroll, NoUnrollOnLoop }
enum ProofAction       { Continue, NextDepth, FoundCounterexample, FoundProof }
```

---

## Strategy Implementations

| Strategy | File | State Type | Theory | Refinement |
|----------|------|-----------|--------|------------|
| `Abstract<F>` | `abstract.rs` | `RefinementState` | Array | Shared graph and policy-driven continued search |
| `AbstractArrayWithQuantifiers` | `array_abstract_with_quantifiers.rs` | `RefinementState` | Array | Quantified axioms sent to Z3 |
| `ConcreteArrayZ3` | `array_concrete.rs` | `RefinementState` | Array | No refinement, direct Z3 |
| `ListAbstract` | `list_abstract.rs` | `ListRefinementState` | List | E-graph with list axioms |

Extensions (via `ProofStrategyExt`):
- `Interpolating` (`interpolate.rs`) - runs SMTInterpol on UNSAT results
- `Repl` (`repl.rs`) - interactive shell at each step

---

## Workspace Members

| Member | Path | Purpose |
|--------|------|---------|
| yardbird | `./` | Main verification tool |
| smt2parser | `./smt2parser` | SMT-LIB 2 parser + VMT support |
| garden | `./garden` | Benchmark runner (config matrix, timeouts, JSON results) |
| coop | `./coop` | PoC examples with `#[ensures]` annotations |
| to_vmt | `./to_vmt` | VMT code generation from Rust |
| vmt_macros | `./to_vmt/vmt_macros` | `#[ensures(...)]` proc macro |
| vmtil | `./to_vmt/vmtil` | VMT Intermediate Language |
---

## Build & Run

```bash
# Build (release with LTO)
cargo build --release

# Run on VMT file
cargo run --release -- -f examples/array/example.vmt -d 10

# Run on SMTLIB file
cargo run --release -- -f examples/smt2/example.smt2

# Run with specific strategy + cost function
cargo run --release -- -f file.vmt -s abstract -c split-cost -d 15

# JSON output for tooling
cargo run --release -- -f file.vmt --json-output

# Run benchmarks
cargo run -p garden -- --config garden/config.yaml

# Run tests
cargo test
cargo test -p smt2parser
```

**Build flags** (`.cargo/config.toml`): Links Homebrew libs (`-L /opt/homebrew/lib`), native CPU optimization (`-Ctarget-cpu=native`).

---

## Key File Quick Reference

| What | Where |
|------|-------|
| Entry point | `src/main.rs` |
| CLI options struct | `src/lib.rs` |
| CEGAR loop | `src/driver.rs` |
| Strategy trait | `src/strategies/proof_strategy.rs` |
| Array abstract strategy | `src/strategies/abstract.rs` |
| Array axioms + saturation | `src/theories/array/array_axioms.rs` |
| Shared candidate construction | `src/rule_matching/candidate_builder.rs` |
| Term extraction | `src/rule_matching/extractor.rs` |
| VMT solver (BMC) | `src/vmt_bmc_session.rs` |
| SMTLIB solver | `src/smtlib_problem.rs` |
| SMTLIB adapter | `src/smtlib_refinement_session.rs` |
| Solver interface trait | `src/problem_context.rs` |
| Theory support trait | `src/theory_support.rs` |
| Z3 term conversion | `src/solver/z3_var_context.rs` |
| Array abstractor (parser) | `smt2parser/src/vmt/array_abstractor.rs` |
| VMT model struct | `smt2parser/src/vmt/mod.rs` |
| BMC builder | `smt2parser/src/vmt/bmc.rs` |
| Quantifier instantiator | `smt2parser/src/vmt/quantified_instantiator.rs` |
| SMT2 AST types | `smt2parser/src/concrete.rs` |
| Cost function trait | `src/policy/term_selection/mod.rs` |
| Instantiation strategy trait | `src/instance_installation/mod.rs` |

---

## Incomplete / TODO Areas

- `Theory::BvList` in VMT mode: `todo!()` at `src/main.rs`
- BvList cost functions: empty module at `src/policy/term_selection/bvlist/mod.rs`
- `PreferConstants` for BvList strategy: `todo!()` at `src/lib.rs`
- List theory: only `AstSize` cost function implemented; other cost functions are `todo!()`
- `AbstractWithQuantifiers` for List: `todo!()` at `src/lib.rs`
- Concrete strategy for List: `todo!()` at `src/lib.rs`
- Decimal, binary, string constants in Z3VarContext: `todo!()` in `z3_var_context.rs`

---

## Screenslaver

A Screenslaver daemon runs at `http://localhost:3000` for browser automation and screenshots.

Use it for any local app port by substituting the target URL, for example `http://localhost:5176/`.

### Create a session

```bash
curl -s -X POST http://localhost:3000/sessions \
  -H 'Content-Type: application/json' \
  -d '{"name":"local-app","url":"http://localhost:5176/","viewport":{"width":1440,"height":900}}'
```

### Run actions

```bash
curl -s -X POST http://localhost:3000/sessions/local-app/actions \
  -H 'Content-Type: application/json' \
  -d '{"actions":[{"action":"html"},{"action":"console"},{"action":"screenshot"}]}'
```

### Navigate and interact

Use a heredoc when values contain special characters.

```bash
curl -s -X POST http://localhost:3000/sessions/local-app/actions \
  -H 'Content-Type: application/json' \
  -d @- <<'EOF2'
{"actions":[
  {"action":"goto","url":"http://localhost:5176/"},
  {"action":"wait","ms":1000},
  {"action":"click","selector":"text=Some text"},
  {"action":"fill","selector":"input","value":"example"},
  {"action":"waitFor","selector":".some-selector"},
  {"action":"screenshot"}
]}
EOF2
```

### Available actions

`goto`, `click`, `fill`, `scroll`, `wait`, `waitFor`, `screenshot`, `html`, `console`

### Screenshots

Screenshot responses include a `"path"` field with an absolute path to the saved image. Use the image viewer tool on that path to inspect it.

### Teardown

```bash
curl -s -X DELETE http://localhost:3000/sessions/local-app
```

---

## Agent skills

### Issue tracker

Issues are tracked as local Markdown under `.scratch/<feature-slug>/issues/`. See `docs/agents/issue-tracker.md`.

### Triage labels

Use the default triage vocabulary: `needs-triage`, `needs-info`, `ready-for-agent`, `ready-for-human`, and `wontfix`. See `docs/agents/triage-labels.md`.

### Domain docs

Use the single-context layout: `CONTEXT.md` and `docs/adr/` at the repository root. See `docs/agents/domain.md`.
