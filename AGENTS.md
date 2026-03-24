# Yardbird Agent Reference

A CEGAR (Counter-Example Guided Abstraction Refinement) tool for automated verification of array-manipulating programs. Yardbird performs bounded model checking on VMT (Verification Modulo Theories) and SMT-LIB format problems, using e-graph-based abstraction refinement with pluggable cost functions.

**Rust edition:** 2021 | **Toolchain:** 1.89.0 | **Key deps:** z3 0.19.3, egg 0.10.0, clap 4.5, serde, tokio

---

## Repository Layout

```
yardbird/                       # Root workspace
  src/                          # Main yardbird binary + library
    main.rs                     # Entry point: mode dispatch (VMT vs SMTLIB)
    lib.rs                      # Library root, CLI options, strategy builders
    driver.rs                   # CEGAR loop orchestrator (check_strategy)
    smt_problem.rs              # VMT temporal system solver (BMC unrolling)
    smtlib_problem.rs           # SMTLIB problem parser + simple solver
    smtlib_smt_problem.rs       # Adapter: SMTLIB -> SolverInterface
    solver_interface.rs         # Trait unifying SMT/SMTLIB problem access
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
    baml_client.rs              # BAML AI verification client
    utils.rs                    # SolverStatistics, general utils
    strategies/
      mod.rs                    # Re-exports all strategies
      proof_strategy.rs         # ProofStrategy + ProofStrategyExt traits
      array_abstract.rs         # Abstract<F> - main CEGAR refinement strategy
      array_abstract_with_quantifiers.rs  # Quantified axiom variant
      array_concrete.rs         # ConcreteArrayZ3 - direct Z3 array theory
      list_abstract.rs          # ListAbstract - list theory refinement
      interpolate.rs            # Interpolating extension
      repl.rs                   # Interactive REPL extension
    theories/
      mod.rs
      array/
        array_axioms.rs         # ArrayLanguage, axioms, e-graph saturation
        array_conflict_scheduler.rs  # Conflict detection + instantiation gen
        array_term_extractor.rs # Cost-based e-class extraction
      list/
        list_axioms.rs          # ListLanguage, list axioms
        list_conflict_scheduler.rs
        list_term_extractor.rs
      bvlist/
        bitvector_list_axioms.rs  # BitVectorListLanguage (incomplete)
    cost_functions/
      mod.rs                    # YardbirdCostFunction trait
      array/
        mod.rs                  # Factory functions for all array costs
        symbol_cost.rs          # BmcCost - structure-based heuristic
        ast_size.rs             # AstSize - minimize expression size
        adaptive_cost.rs        # AdaptiveCost - depth-aware heuristic
        split_cost.rs           # SplitCost - synthesizes critical terms
        prefer_read.rs          # PreferRead - bias toward reads
        prefer_write.rs         # PreferWrite - bias toward writes
        prefer_constants.rs     # PreferConstants - bias toward constants
      list/
        mod.rs
        ast_size.rs
      bvlist/
        mod.rs                  # Empty (TODO)
    instantiation_strategy/
      mod.rs                    # InstantiationStrategy trait
      full_unroll.rs            # FullUnroll - unroll all at each depth
      no_unroll_on_loop.rs      # NoUnrollOnLoop - selective unrolling
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
  baml_rust/                    # BAML AI verification API client
  baml_schemas/                 # BAML schema definitions
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

---

## Execution Flow

### CLI Options (`src/lib.rs:48-105`)

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
  --repl                     Interactive mode
  --dump-solver <PATH>       Dump Z3 state on unsat
  --track-instantiations     Enable unsat core tracking
  --dump-unsat-core <PATH>   Export unsat core JSON
```

### Mode Dispatch (`src/main.rs:12-35`)

```
main()
  ├─ .smt2 extension -> run_smtlib_mode()
  │   ├─ Simple mode (Concrete + BmcCost) -> SMTLIBSolver::execute()
  │   └─ Strategy mode -> SMTLIBSolver::execute_with_strategy()
  └─ .vmt extension -> run_vmt_mode()
      ├─ Theory::Array  -> Driver::check_strategy(build_array_strategy())
      ├─ Theory::List   -> Driver::check_strategy(build_list_strategy())
      └─ Theory::BvList -> todo!()
```

### CEGAR Loop (`src/driver.rs:255-324`)

```
check_strategy(target_depth, strategy):
  model = strategy.configure_model(model)    // abstract array ops
  smt_problem = SMTProblem::new(model, strategy)
  for depth in 0..target_depth:              // outer BMC loop
    for refinement_step in 0..250:           // inner refinement loop
      smt_problem.unroll(depth)
      state = strategy.setup(smt, depth)
      match smt_problem.check():
        Unsat   -> strategy.unsat()   -> NextDepth
        Sat     -> strategy.sat()     -> Continue (refine) or FoundCounterexample
        Unknown -> strategy.unknown() -> error
      match action:
        Continue            -> strategy.finish(state, smt)  // add instantiations
        NextDepth           -> continue to next depth
        FoundCounterexample -> return error
        FoundProof          -> return result
    TooManyRefinements error if inner loop exhausted
```

---

## Core Traits

### ProofStrategy (`src/strategies/proof_strategy.rs:23-56`)

```rust
pub trait ProofStrategy<'ctx, S> {
    fn get_theory_support(&self) -> Box<dyn TheorySupport>;
    fn configure_model(&mut self, model: VMTModel) -> VMTModel;  // default: identity
    fn n_refines(&mut self) -> u32;                               // default: 250
    fn setup(&mut self, smt: &dyn SolverInterface, depth: u16) -> Result<S>;
    fn unsat(&mut self, state: &mut S, smt: &dyn SolverInterface) -> Result<ProofAction>;
    fn sat(&mut self, state: &mut S, smt: &dyn SolverInterface, step: u32) -> Result<ProofAction>;
    fn unknown(&mut self, state: &mut S, smt: &dyn SolverInterface) -> Result<ProofAction>;
    fn finish(&mut self, state: S, smt: &mut dyn SolverInterface) -> Result<()>;
    fn result(&mut self, model: &mut VMTModel, smt: &dyn SolverInterface) -> ProofLoopResult;
}
```

### SolverInterface (`src/solver_interface.rs`)

```rust
pub trait SolverInterface {
    fn get_model(&self) -> &Option<z3::Model>;
    fn rewrite_term(&self, term: &Term) -> Dynamic;       // Term -> Z3 AST
    fn get_all_subterms(&self) -> Vec<&Term>;
    fn get_interpretation(&self, model: &z3::Model, z3_term: &Dynamic) -> Dynamic;
    fn add_instantiation(&mut self, inst: Instance) -> bool;
    fn get_instantiations(&self) -> Vec<Term>;
    fn get_variables(&self) -> &[Variable];
    fn get_reads_and_writes(&self) -> ReadsAndWrites;
    fn get_array_types(&self) -> Vec<(String, String)>;
    fn get_solver_statistics(&self) -> SolverStatistics;
    fn get_reason_unknown(&self) -> Option<String>;
    // ... more
}
```

Implementations: **SMTProblem** (VMT temporal), **SMTLIBSMTProblem** (stateless SMTLIB)

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

### YardbirdCostFunction (`src/cost_functions/mod.rs`)

```rust
pub trait YardbirdCostFunction<L>: egg::CostFunction<L, Cost = u32> + Clone
where L: egg::Language + egg::FromOp
{
    fn get_string_terms(&self) -> Vec<String>;
    fn get_reads_and_writes(&self) -> ReadsAndWrites;
    fn get_parsed_terms(&self) -> Vec<egg::RecExpr<L>>;
}
```

### InstantiationStrategy (`src/instantiation_strategy/mod.rs`)

```rust
pub trait InstantiationStrategy: Debug + Send {
    fn clone_box(&self) -> Box<dyn InstantiationStrategy>;
    fn on_generate(&mut self, inst, instantiations, depth, bmc_builder, ...);
    fn on_loop(&mut self, depth, instantiations, bmc_builder, ...);
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

### ArrayLanguage (`src/theories/array/array_axioms.rs:14-40`)

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

Type aliases: `ArrayExpr = egg::RecExpr<ArrayLanguage>`, `ArrayPattern = egg::PatternAst<ArrayLanguage>`

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

`src/strategies/array_abstract.rs` implements `ProofStrategy<ArrayRefinementState>`:

```
setup(depth):
  - Create fresh EGraph<ArrayLanguage>
  - Collect array_types from model or solver

sat(state, smt, refinement_step):
  1. Get Z3 model from counterexample
  2. update_with_subterms(): for each subterm in problem:
     - Translate term -> ArrayExpr, add to e-graph
     - Get model interpretation, parse, add to e-graph
     - Union term with its interpretation (model assignment)
     - Rebuild e-graph
  3. saturate_with_array_types():
     - Create ArrayConflictScheduler with cost function
     - Run egg::Runner with array axioms on e-graph
     - Scheduler INTERCEPTS rewrites that would create new equalities
     - Each intercepted rewrite = conflict = new instantiation
     - Returns (instantiations, const_instantiations)
  4. Extend state with discovered instantiations
  -> ProofAction::Continue

finish(state, smt):
  - Convert ArrayExpr instantiations -> SMT Terms via expr_to_term()
  - Rewrite via UnquantifiedInstantiator (handles variable naming)
  - Add to solver via smt.add_instantiation()
  -> Next check() will include these constraints

unsat(state):
  -> ProofAction::NextDepth (all counterexamples at this depth ruled out)
```

### Conflict Detection (`src/theories/array/array_conflict_scheduler.rs`)

The `ArrayConflictScheduler` wraps egg's scheduler to intercept axiom applications:

```
apply_rewrite(egraph, rewrite, matches):
  if already have instantiations: return 0  // stop early
  for each match:
    compute RHS e-class for this match
    if LHS e-class != RHS e-class:
      // Axiom would create new equality -> CONFLICT
      Extract best terms using cost function
      Build instantiation term (equality or implication)
      if cost >= 100: push to const_instantiations
      else: push to instantiations
  return 0  // never actually apply the rewrite
```

### Term Extraction (`src/theories/array/array_term_extractor.rs`)

The `ArrayTermExtractor` provides progressive refinement:
- Pre-caches terms by cost for each e-class
- At refinement_step N, selects the Nth-best term representation
- Falls back to standard egg extraction if step exceeds cache

### Cost Functions (Array)

All in `src/cost_functions/array/`:

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

### SMTProblem (VMT Mode) (`src/smt_problem.rs`)

Represents a temporal transition system for BMC:

```rust
pub struct SMTProblem {
    z3_var_context: Z3VarContext,          // term <-> Z3 mapping
    bmc_builder: BMCBuilder,              // time-step indexing
    init_assertion: Term,                  // initial state formula
    trans_assertion: Term,                 // transition relation
    depth: u16,                            // current BMC depth
    instantiations: Vec<Instance>,         // quantifier instantiations
    subterm_handler: SubtermHandler,       // subterm extraction
    solver: z3::Solver,                    // Z3 instance
    newest_model: Option<z3::Model>,       // last SAT model
    instantiation_strategy: Box<dyn InstantiationStrategy>,
    // ... tracking fields
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
- `SMTLIBSolver` - executes commands sequentially (assert, check-sat, push/pop)

### Z3VarContext (`src/z3_var_context.rs`)

Converts SMT2 parse tree to Z3 AST. Handles:
- Constants: numerals, hex (-> BV), true/false
- Applications: arithmetic, boolean, array (select/store/const), bitvector ops
- Quantifiers: forall with fresh variables + scope management
- Indexed operations: extract, zero_extend, sign_extend
- BV operations: bvadd, bvsub, bvmul, bvand, bvor, bvxor, bvnot, bvneg, shifts, comparisons

---

## Key Data Structures

### ProofLoopResult (`src/driver.rs:14-22`)

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

### ArrayRefinementState (`src/strategies/array_abstract.rs:58-64`)

```rust
pub struct ArrayRefinementState {
    pub depth: u16,
    pub egraph: egg::EGraph<ArrayLanguage, ()>,
    pub instantiations: Vec<ArrayExpr>,
    pub const_instantiations: Vec<ArrayExpr>,
    pub array_types: Vec<(String, String)>,
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

### Driver Errors (`src/driver.rs:181-209`)

```rust
pub enum Error {
    Counterexample,                           // real counterexample found
    NoProgress { depth, instantiations },     // refinement stalled
    TooManyRefinements { n_refines, depth },  // hit 250 limit
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
| `Abstract<F>` | `array_abstract.rs` | `ArrayRefinementState` | Array | E-graph saturation, 250 refines/depth |
| `AbstractArrayWithQuantifiers` | `array_abstract_with_quantifiers.rs` | `ArrayRefinementState` | Array | Quantified axioms sent to Z3 |
| `ConcreteArrayZ3` | `array_concrete.rs` | `ArrayRefinementState` | Array | No refinement (n_refines=1), direct Z3 |
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
| baml_rust | `./baml_rust` | BAML AI verification API client |

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
| Entry point | `src/main.rs:12` |
| CLI options struct | `src/lib.rs:48-105` |
| CEGAR loop | `src/driver.rs:255-324` |
| Strategy trait | `src/strategies/proof_strategy.rs:23-56` |
| Array abstract strategy | `src/strategies/array_abstract.rs:86-219` |
| Array axioms + saturation | `src/theories/array/array_axioms.rs` |
| Conflict detection | `src/theories/array/array_conflict_scheduler.rs` |
| Term extraction | `src/theories/array/array_term_extractor.rs` |
| VMT solver (BMC) | `src/smt_problem.rs` |
| SMTLIB solver | `src/smtlib_problem.rs` |
| SMTLIB adapter | `src/smtlib_smt_problem.rs` |
| Solver interface trait | `src/solver_interface.rs` |
| Theory support trait | `src/theory_support.rs` |
| Z3 term conversion | `src/z3_var_context.rs` |
| Array abstractor (parser) | `smt2parser/src/vmt/array_abstractor.rs` |
| VMT model struct | `smt2parser/src/vmt/mod.rs` |
| BMC builder | `smt2parser/src/vmt/bmc.rs` |
| Quantifier instantiator | `smt2parser/src/vmt/quantified_instantiator.rs` |
| SMT2 AST types | `smt2parser/src/concrete.rs` |
| Cost function trait | `src/cost_functions/mod.rs` |
| Instantiation strategy trait | `src/instantiation_strategy/mod.rs` |

---

## Incomplete / TODO Areas

- `Theory::BvList` in VMT mode: `todo!()` at `src/main.rs:241`
- BvList cost functions: empty module at `src/cost_functions/bvlist/mod.rs`
- `PreferConstants` for BvList strategy: `todo!()` at `src/lib.rs:230`
- List theory: only `AstSize` cost function implemented; other cost functions are `todo!()`
- `AbstractWithQuantifiers` for List: `todo!()` at `src/lib.rs:255`
- Concrete strategy for List: `todo!()` at `src/lib.rs:258`
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
