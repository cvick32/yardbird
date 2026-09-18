# YardbirdPolicy design

Updated 2026-09-18. Design incorporating the review interview. The policy and
array/quantifier module extraction, replaceable effort dispatch, shared vocabulary,
neutral instantiation modules, continued search and versioned training-database
policy observations are implemented. Alternative effort policies and more informed
adaptive heuristics remain later work. See the
[implementation progress](yardbird-policy-progress.md) for scope and validation.
Based on [the handoff](yardbird-policy-handoff.md) and the current working tree,
including its uncommitted dependency requests and signed matching plans.

Review decisions: one shared graph with staged vocabulary growth and immutable
search rounds; adaptive winner allowances from effort policy; policy-owned phase
gating and fairness; continued search until an external limit; first-pass instance
selection parity for array programs and current distributed-protocol progress.
Exact Rust types remain illustrative. Behavioral changes are separated from the
initial parity checkpoint below.

Compatibility decision (2026-09-17): backward compatibility is not a requirement.
Change APIs, configuration and file formats when the design benefits, updating
in-repository callers directly. Do not add old-signature wrappers, aliases or
deprecation paths just to preserve prior interfaces. The old implementation is
a behavioral baseline for comparing selected instances and protocol progress;
it is not an API contract. Intentional search changes remain separately measured.

## Recommendation

Make `YardbirdPolicy<F>` a composed, configured policy, owned by `Abstract<F>`.
Its three replaceable parts are term selection, whole-instantiation selection,
and proof effort. Reuse the existing term and ranker interfaces where useful;
introduce an effort interface for the choices currently embedded in control flow.

Separate array refinement and general quantifier refinement into two modules
under one refinement coordinator. `Abstract<F>` initially remains the public
`ProofStrategy` adapter and hosts that coordinator. The policy schedules work
across both modules; neither module owns an independent proof loop. Shared
instantiation machinery supports both modules without becoming array-owned
in the eventual organization.

Both modules search one coordinator-owned e-graph. Construction is mutable and
staged; matching and extraction receive immutable access within each search
round. The modules retain separate search state, not separate graph ownership.

Keep `F: ArrayCostFactory` initially. The factory returns a concrete, cloneable
Egg cost function, can expose a contextual selector, and already accommodates
the logistic-regression model. Erasing this generic would add migration work
without improving the scheduling seam.

The engine executes operations and establishes their logical validity. Policy
chooses among valid operations and candidates. Policy cannot assert formulas,
declare a proof/counterexample, reinterpret a model fact as an axiom, or make an
incomplete search complete.

## Refinement architecture

```text
                      YardbirdPolicy
                chooses work and candidates
                            |
                   Refinement coordinator
                    /                 \
           Array refinement     Quantifier refinement
                    \                 /
                One shared, read-only search graph
                            |
                Shared assertion/provenance ledger
                            |
                    Existing SMT solver
```

| Module | Responsibility |
|---|---|
| Coordinator, initially inside `Abstract<F>` | Own/build/version the shared graph, dispatch selected work, maintain shared selection history and installation accounting, connect to the existing driver's solver/model lifecycle |
| Array refinement | Built-in array axioms, array vocabulary requirements, specialized array searches and guarded read consequences |
| Quantifier refinement | Input binder compilation, witnesses and valid directions, dependency discovery/requests, triggered/domain searches and deferred expansion |
| Shared instantiation machinery | Term representation, matching primitives, extraction, grounding, candidate selection, provenance and work-report types |
| Existing driver and solver | BMC, solver checks, concrete validation where permitted, authoritative proof/counterexample outcomes |

`PreparedQuantifierSearch` now retains compiled searches and model-scoped caches,
and borrows the coordinator's `RefinementGraph` for matching. It imports
`ArrayLanguage`, `CompiledQuantifiedRule`, candidate batches, extraction and cost
context through array modules. Preserve that reuse initially; move genuinely
shared machinery into neutral modules in a later mechanical refactor. Built-in
array axioms can still use the same instantiation machinery as input binders.

Call the second module a quantifier engine, because its formulas can contain
array operations and other theory terms. The division follows refinement
responsibility, not disjoint term vocabularies. Preserve the current ownership
of transition guards, lambda lowering and array-sort translation during the
first extraction rather than forcing them into an artificial theory partition.

Each module describes available operations and executes a selected operation
against the current read-only model/context with an explicit allowance. It
returns candidates or existing guarded-update proposals, provenance, work
consumed and continuation/exhaustion information. The coordinator routes term
and instance policy into this execution and retains the existing validation and
selection ordering. Module results cannot assert directly or claim a proof.
Start with two concrete modules and typed operation dispatch; a universal
theory-plugin trait is not required to establish this seam.

### Shared graph and staged construction

Review clarification (2026-09-17): the target is one shared search vocabulary.
Module-specific admission restrictions are a temporary measure to preserve the
selection baseline during rearchitecture. After that migration, remove those
restrictions and express term preferences through replaceable policies. Sort
correctness, formula validity and explicit global vocabulary growth remain
engine requirements. Do not turn the temporary scopes into permanent separate
module views or graphs. The cleanup checkpoint has now removed those restrictions.

Current matching and extraction already accept `&EGraph`; Egg does not require
mutation during matching. The coordinator builds or expands the graph, applies
the permitted model-equivalence unions, calls `rebuild()`, and then exposes only
immutable access to the modules. Instance generation never applies theory
equalities back into this model graph as though the model already satisfied them.

The effort policy requests vocabulary growth between search rounds. The
coordinator executes it and advances a graph version before either module resumes.
Keep model and graph versions distinct: the same solver model can support several
successively broader graph stages. A fresh model invalidates the old model graph.
One active graph is sufficient; immutable access does not require keeping a copy
per module or a persistent history of graph snapshots.

The shared builder groups model values by sort, adds typed domain markers and
keeps solver-private values out of the candidate vocabulary. Array construction
can add well-typed model literals. Both admission paths update the same graph.
Array matching now sees terms admitted by binder preparation immediately. The
temporary structural admission metadata and matching-prefix filtering are gone.
Staged growth controls the shared vocabulary; policy controls search timing,
term preferences and whole-instance selection. Shared language, matching,
grounding, extraction, ranking and instance provenance live under `instantiation`.
Binder lowering, dependency guidance, matching plans and provenance live under
`quantifiers`; array axioms and array construction remain under `theories::array`.

Test the effect of additional nodes and congruence on matches and winners.
Do not promise parity merely because construction order is deterministic; verify
instance selection against the captured baseline. If sharing changes selection,
resolve that explicitly rather than silently weakening the parity criterion.

### Cooperation and model refresh

Modules cooperate through installed lemmas, the common term/provenance context,
and subsequent solver models. For example, a binder instance of
`forall i. P(select(A, i))` produces `P(select(A, k))`. Given
`A = store(B, k, v)`, array refinement can supply the read-after-write instance;
the solver can combine them to derive `P(v)` and contradict an asserted
`not P(v)`. New instance terms become available to the other module through
the existing problem context on the appropriate refresh.

The coordinator preserves the distinction between generation, selection and
actual installation, and returns to the solver at the current return points.
After a fresh solver model, invalidate both modules' model-local state; retain
policy scheduling positions and the shared history ledger. Same-model graph
expansion invalidates graph-dependent state in both modules. Cached evaluations
of unchanged ground formulas can survive graph expansion while their model is
unchanged; caches keyed by equality IDs cannot be assumed valid. Do not eagerly
admit speculative instance terms outside the policy-requested construction stage.

Equality IDs identify classes only within their graph version and model. Both
modules can use them in that scope; they are not permanent semantic facts or
persistent policy identity. Model equality may guide matching but cannot be
promoted to a persistent lemma. Two empty or budget-exhausted module results do
not establish quantified validity or a concrete counterexample.

Separate solvers, direct module-to-module callbacks, mutation during matching,
and new equality-exchange protocols are outside this migration. Cooperation uses
the shared graph for search and the existing solver for installed consequences.

## Existing choices and their destination

| Existing choice | Proposed owner | Initial adapter/behavior |
|---|---|---|
| Cost construction and contextual representative selection | Term component | `ArrayCostFactory`, `YardbirdCostFunction`, `ContextualCandidateSelector` |
| History-aware representative preferences and tie-breaking | Term component's selection semantics | Existing extractor behavior, unchanged |
| Whole-candidate comparison, source preference, eligibility, provenance requirements | Instance component | `InstantiationRanker`, including all its methods |
| Dynamic winner allowance for an operation | Effort component | Initially use the current fixed `winners_per_group` value |
| Choosing winners within the allowance, per-kind source limits, grouping and selection order | Instance component | Existing ranker and `InstantiationBatch` algorithm |
| Dependency-first scheduling, every-eighth-step fairness, request ordering | Effort component | Current dependency behavior |
| Choice of refinement module, phase order, rule rotation, continuation, return to driver | Effort component | Current interleaving in `sat` and binder scheduling behavior |
| Dependency/search budgets and array backoff allowances | Effort component | Existing values and accounting units |
| Staged vocabulary growth strategy | Effort configuration, builder adapter | Coordinator owns graph mutation; reconcile array/binder vocabulary requirements |
| Quantifier compilation, valid directions, signed alternatives and dependency discovery | Quantifier module | Existing mechanisms |
| Matching, extraction and grounding | Shared machinery invoked by each module | Existing specialized searches remain available |
| Model checks, novelty, installability, provenance, assertion materialization | Coordinator and shared machinery | Existing checks retained at their current execution points |
| Full-unroll/no-unroll-on-loop placement | Existing placement interface | Separate from proof effort |

This division does not require moving every implementation into a new directory.
For example, the engine's batch module can execute selection using the instance
component while retaining the exact current filtering and grouping algorithm.

## Interface shape

Illustrative Rust; auxiliary types below describe the intended seam, not a
commitment to exact spelling:

```rust
pub struct YardbirdPolicy<F: ArrayCostFactory> {
    terms: TermSelection<F>,
    instances: InstanceSelection,
    effort: Box<dyn ProofEffort>,
}

pub struct TermSelection<F: ArrayCostFactory> {
    config: F::Config,
    // Keeps F's existing contextual selector and extraction behavior.
}

pub struct InstanceSelection {
    ranker: Box<dyn InstantiationRanker>,
}

pub trait ProofEffort {
    fn choose(&mut self, context: &EffortContext<'_>) -> EffortDecision;
    fn observe(&mut self, event: &EffortEvent);
}

pub enum EffortDecision {
    Execute { operation: OperationId, allowance: WorkAllowance },
    ReturnToDriver,
}
```

Use private fields with constructors and replacement methods. Callers configure
one policy; component authors retain access to the separate interfaces. Existing
`Abstract::new` takes the policy directly. Configure term, instance and effort
choices on the policy; remove duplicate policy builders on the strategy and
update callers directly.

The coordinator receives one policy and owns the two refinement modules. It is
the only caller that dispatches effort decisions to them. Module operations can
use shared extraction/selection services without acquiring a second policy or
mutating the solver. Keep the existing `ProofStrategy` interface at the driver
seam; do not implement that full lifecycle separately for each module.

`EffortContext` supplies depth, refinement step, model and graph versions, current
selection-history revision, pending selected work, engine work reports, and an
ordered, lightweight view of currently executable operations from both modules.
Each operation identifies its owning module. Operations describe
dependency discovery, a dependency request, a binder rule/alternative/direction
page, guarded read refinement, or array-stage work. Do not materialize matches or
extract representatives merely to describe choices.

Operations use opaque, module- and version-scoped handles at runtime and symbolic
descriptors for observation. The coordinator and owning module reject
stale/unknown handles, invalid directions, ill-typed bindings, and invalid
allowances. The engine offers only mechanically valid operations. Policy may
further gate those operations, such as allowing expansion only after an array
pass fails. That gate belongs to the replaceable policy, not the coordinator.
Engine withholding is justified by mechanical prerequisites or unsupported
operations, not by a preferred search order. Expensive discovery itself is an
operation; unseen paths are not falsely advertised as available choices.

`WorkAllowance` uses explicit dimensions, not a universal scalar: page size,
per-rule/pass limit, dependency request count, discovery work, structural bounds,
and a winner allowance. Effort policy may adapt the winner allowance per
quantifier/operation; instance policy chooses which candidates survive within it.
The initial effort implementation supplies the existing fixed `winners_per_group` default and
retains current per-category/group and per-kind source-limit behavior. The
allowance is an upper limit, not a promise that enough eligible candidates exist.
Matching remains responsible for prefix replay, lookahead, offsets,
filters and actual work accounting. Compiler fallback bounds for signed plans
remain engine settings, recorded with the run rather than presented as ranking.

`EffortEvent` covers model/pass lifecycle, operation completion, installation
results, and subsequent solver outcomes. Immediate results report generated,
eligible and selected candidates separately, consumed work, continuation state,
and bounded exhaustion. Errors propagate through the engine; they are not empty
candidate batches.

`ReturnToDriver` preserves the current distinction between installing selected
work and returning empty-handed for concrete validation or another search stage.
It does not force a solver check on an unchanged quantified abstraction.

There is no discretionary `StopIncomplete` action in the target effort interface.
The intended policy keeps working until a conclusive engine result, external
timeout/resource limit, or cancellation. It can leave a path, change modules,
raise search caps or request term growth. Local exhaustion should trigger another
search decision rather than a heuristic whole-run stop. Genuine execution errors
or unsupported required expansion still report explicit failures; this contract
does not justify spinning on an unchanged exhausted operation. Concrete growth
mechanisms must exist to honor a continuation request.

Continued search deliberately replaces the initial parity checkpoint's
`AbstractionExhausted` termination. The error variant is removed. Neither timeout
nor local exhaustion becomes a proof or counterexample.

After an empty search through the initial graph stages and binder expansion,
`DefaultEffort` alternates widening allowances and requesting `GrowVocabulary`.
Widening doubles winner, matching and dependency allowances, with checked
machine-size bounds. Vocabulary growth enumerates applications of declared
functions over available terms of the required sorts, integer successor/predecessor
expressions, and Boolean negations. Each operation bounds construction attempts;
constructor products are traversed deterministically across calls. New symbolic
terms and their typed model evaluations enter the same graph, without assertions.
This is a first continuation heuristic, not a completeness guarantee or a learned
assessment of which quantifier needs more information.

Each pass returns to driver checkpoints. The abstract strategy has no fixed
250-refinement limit. Cooperative wall timeouts apply in both VMT and strategy-based
SMT-LIB mode; individual solver/search operations can overrun the deadline.
Concrete UNSAT validation is reused for the unchanged BMC depth or SMT-LIB query.
Abstract solver checks still require new assertions; input quantifiers are not
delegated to concrete validation. A new model resets widened default allowances
and model-specific growth state, retaining policy rule-scheduling bookmarks.

### Implemented effort checkpoint (2026-09-17)

`YardbirdPolicy::with_effort` now replaces a `ProofEffort` implementation.
The concrete interface uses two levels: `choose` selects dependency discovery,
a directed request page, a binder phase, guarded consequences, staged array
construction, shared vocabulary growth or array candidates; `choose_binder_rule` chooses each pending rule page inside
a binder phase. Returning `None` from the latter pauses the phase without
certifying it empty. The next phase operation can use a new allowance. This
keeps compiled matching details internal while making phase and rule scheduling
replaceable. `DefaultEffort` owns both decisions, including its round-robin
bookmarks and every-eighth-pass dependency bypass.

Each execution carries `WorkAllowance`: winner count, binder page and search
limits, array search bounds, dependency discovery bounds and vocabulary work. Discovery can be
requested again with larger bounds. Default request-count and phase scheduling
live in `DefaultEffort`; there is no coordinator fairness override. Opaque
operation handles expire at the next offer. Pending instances participate in
novelty checks before installation, so a policy may collect several batches.

`--profile` emits ordered effort records with offered symbolic work, the chosen
operation, allowance, time, work report and selected abstract-instance links.
Page records share their parent operation ID. Reports distinguish returned
candidates, selected instances, substitution work, dependency work and bounded
exhaustion; existing candidate counters retain detailed filtering counts.
Installation and solver outcomes are delivered to the policy separately.
Versioned training-database effort records now link choices to surrounding solver
checks, candidate records and installation attempts. Timeout and failure traces are
retained. These observations do not claim causal proof credit.

The empty-pass key includes graph version, allowance, pending instances,
refinement step and selection history. Graph growth restarts offsets, clears
equality-ID obligations and dependency discovery, and refreshes representatives.
Exact symbolic formula evaluations survive within the same model. A changed
allowance also reruns matching. A new solver model clears these caches and
offsets; scheduling bookmarks remain policy state. Empty completed searches
now lead to another policy pass with wider allowances or vocabulary growth.

## Composition and independence

The initial effort implementation is `DefaultEffort`, internally composed of a schedule
across refinement modules/phases, dependency guidance and rule scheduling. In the
explicit-effort migration, extract dependency guidance and round-robin scheduling
into replaceable subcomponents. They retain discovery order, fairness,
rotation and budgets exactly before adding any alternate behavior.

Cross-module allocation belongs to this same effort component. Array and
quantifier modules expose work; they do not each run a hidden top-level schedule
or receive separate, competing global budgets. Existing specialized enumeration
remains mechanism. This permits an effort ablation to change cooperation while
holding both modules and the term/instance components fixed.

Fairness belongs entirely to replaceable effort policies. The coordinator does
not force neglected rules/modules to run. The baseline policy preserves the
every-eighth-step bypass and round-robin positions, but other policies may change
or omit them. Starvation under a poor policy is observable policy behavior, not
permission for the coordinator to impose a hidden fallback schedule.

Keep discovery's logical producer/path construction in the engine. Guidance
decides whether to discover, which returned paths/requests to pursue, and how
much work to spend. Round-robin chooses the next pending compiled rule; each
signed alternative retains its independent engine cursor. The engine must not
silently rotate to another rule after policy has chosen one.

Replacing term selection leaves the instance and effort implementations and
configuration fixed; replacing either of the latter leaves the others fixed.
This does not promise identical downstream decisions: both current rankers read
the candidate's term cost, and different winners can change subsequent solver
models. Record that dependency explicitly in ablation descriptions.

Holding an effort policy fixed means holding its implementation, initial
configuration and update rules fixed, not replaying identical quantifier choices
after another component changes the models. Those downstream changes are part
of a term-selection ablation. Prescribing an identical action schedule answers
a different experimental question.

Do not introduce a second contextual term-selector interface during the facade
migration. Existing learned models continue through `contextual_selector()`;
candidate enumeration, source vocabulary restrictions, feature construction and
fallback behavior stay as they are.

## State ownership and lifecycle

| State | Owner and lifetime |
|---|---|
| Resolved initial configuration, learned parameters and adaptation rules | Policy identity; fixed for a run |
| Effective per-operation allowances, including winner counts | Effort runtime state; may adapt and must be recorded |
| Rule scheduling positions and adaptive scheduling memory | Effort component; survive model refresh, reset on problem configuration |
| One e-graph, model/graph versions and staged builder progress | Coordinator; graph frozen during search and expanded between rounds |
| Equality-ID indexes, extraction caches, per-rule/per-alternative offsets and request cursors | Respective module/shared machinery; invalidate on graph or model change |
| Ground-formula evaluation cache keyed by symbolic terms | Model-scoped; can survive graph-only growth when formula/environment are unchanged |
| Obligation caches keyed by equality IDs | Quantifier module; graph- and model-scoped |
| Dependency discovery completion/result | Quantifier module; invalidate when its model or relevant graph/vocabulary context changes |
| Term selection counts and decision accounting | Coordinator-owned run ledger exposed read-only to policy; shared across modules with current updates preserved |
| Empty-pass cache | Quantifier module; model/graph/pass, allowance and selection-context scoped |
| Installed formulas, provenance and assertion accounting | Shared ledger and existing solver/session infrastructure; coordinator routes installation |
| Solver and proof status | Existing driver/solver; no independent module proof outcomes |

Preserve `start_phase` semantics: a new pass restarts match offsets, even on the
same model, while retaining the scheduling position. Graph expansion also resets
match offsets because the enumeration may change. Fresh model state never
inherits old equality IDs or evaluation results. Scheduling positions survive
both changes, under control of the effort policy.

The empty-pass key includes the graph version, refinement step, exact selection
counts, pending instances and allowance inside the model's prepared state.
Include any additional policy context revision if it can vary during that state.
A cached bounded failure must not hide work enabled by a larger allowance
or changed selection context. Do not replace exact history equality with a
guessed cache equivalence in the facade.

An empty-pass entry means "no selected instance under these conditions," not
necessarily "no matches." Reuse the unsuccessful result only for matching
conditions initially. A larger search selecting nothing does not in general
justify skipping a smaller search: full-array ranking precedes novelty checking,
so an already-installed cheap winner can suppress a novel, more expensive
candidate. If that cheap winner is absent from the smaller search, the novel
candidate can win. Preserve valid cached work separately from reusing the
conclusion of a failed selection pass.

The ledger is not simply a count of installed winners: full-array attempts can
retain extraction history after novelty rejection. Preserve these updates and
their ordering in `absorb_candidates`.

## Exact baseline behavior for the parity checkpoint

This section records the historical parity checkpoint. The implemented default
now extends its final empty pass with widening and vocabulary growth.

The baseline schedule is a state machine with driver re-entry:

1. If allowed this step and not already searched on this model, discover
   dependency paths; visit their unique requests in existing prerequisite-first
   order, one page per request, up to 32 attempted requests. Stop at the first
   selected batch. Skip guidance when `refinement_step % 8 == 7`.
2. Search ordinary witnesses; return on a selected batch.
3. Select violated guarded read updates when configured; return on selection.
4. Ask the configured builder for one array growth stage. If a stage exists,
   generate/select array work and return if selected. If this array selection
   yields nothing, search triggered conflicts, then domain conflicts only if
   triggered work selected nothing. Return to the driver even when no work was
   selected. Builder exhaustion instead takes the expansion path in step 5.
5. On driver re-entry with the same model, start through this flow again,
   respecting dependency and empty-pass caches. Concrete validation remains
   where the driver currently permits it. Only when the builder reports
   exhausted does this flow attempt binder expansion; if expansion yields
   nothing, preserve `AbstractionExhausted`.

Ordinary binder passes rotate one pending compiled rule per page and continue
past satisfied/known prefixes until something is selected or bounded work ends.
The next-rule position is updated after each page, including unsuccessful pages.

Keep page size 100 and limit 65,536 per compiled rule per pass, including the
existing growing-prefix/lookahead implementation. Keep dependency bounds of 64
demand atoms, 128 helper evaluations, 512 shared work units, eight links and 16
paths. Keep array enumeration's separate 1,000 initial limit and 15 backoff
rounds. None of these limits establish quantified validity.

Selection invariants deserve explicit regression coverage:

- `TermCostInstantiationRanker` uses ascending canonical expression ties;
  `PreferSourceInstantiationRanker` reverses equal-cost expression ties.
- Full-array work selects within rule/root groups before novelty checks and
  does not promote a replacement when a winner is already known.
- Source-array work selects after eligibility/novelty, using a total source
  winner budget and per-kind limits, then orders source assertions by ranker.
- Guards retain one winner per rule; binders retain their existing grouping.
- Provenance requirements, model-check shortcuts, learned-selector fallback,
  selected/unselected records and history accounting remain unchanged.

## Configuration and scope

The input configuration and construction code select the term implementation,
instance ranker, effort settings and graph builder. Components do not need
self-description methods or a parallel descriptor/fingerprint hierarchy.
Any experiment metadata should come from those existing inputs at the run
boundary, including learned model contents when needed for replay.

Cross-module scheduling choices belong in the effort configuration.
Initially module composition follows existing options/input capabilities; do not
add array-only or quantifier-only CLI modes as part of the facade. A future mode
that omits required refinements must report its resulting incompleteness.

Change CLI spelling and configuration interfaces when useful; preserve search
defaults and behavior during the structural parity checkpoint.
Initially translate existing options into the policy internally;
no new CLI flag is needed for the facade. If named presets are later exposed,
resolve preset defaults first and explicit component overrides second. Emit the
fully resolved result so an overridden preset remains reproducible.

Record a separate run manifest for input hash, source snapshot/build identity,
solver/version/options, placement, encodings/preprocessing, auxiliary extensions
and other search-relevant settings. A dirty flag alone cannot identify this
uncommitted baseline. Named policy identity does not claim to identify the entire
experiment, nor to guarantee deterministic solver behavior across versions.

Deterministic repeatability is the intended behavior under fixed input, build,
solver configuration, policy configuration and initial state. Resolve tie order
explicitly and record seeds if any randomized mechanism is introduced. Adaptive
allowances do not inherently prevent deterministic replay: their update rules
and observations determine the choices. Timing-based adaptation can change those
choices, so the baseline should not introduce it implicitly; record such timing
inputs if a later policy uses them.

Wall-clock timeouts can interrupt identical logical searches at different points.
Use deterministic work/check cutoffs when comparing instance sequences, and
report timing/timeout outcomes separately. A preset name alone is insufficient
when its options or learned-model file contents have changed.

First scope: `Abstract<F>` as the coordinator adapter and its two refinement
modules, including SMT-LIB callers that use it. Concrete and quantified-array
strategies, List and incomplete BvList implementations are not redesigned;
update their call sites directly when shared interfaces change.
Conditional-history extensions keep their current shared cost
configuration; placement, property-check mode, preprocessing and IC3IA remain
separate and appear in the run manifest.

A future combination of native solver arrays with Yardbird-managed quantifiers
would be a useful demonstration of the seam, but requires a separate capability
and soundness review. This plan does not redesign concrete strategies to add it.

## Observation and training

Extend the existing training system, not a parallel logger. It already provides
term `DecisionRecord`s, selected/unselected `AbstractInstantiationRecord`s,
indexed assertion provenance, UNSAT events, a `TrainingSession`, no-op/Postgres
loggers, and migrations through `006_instantiation_substitutions`.

Add versioned effort decision/outcome records through that same pipeline when
explicit effort lands. Record observed context, the offered symbolic choices,
policy gating decisions, chosen module/operation, model/graph versions, requested
allowance including winner count, actual work and stop reason. Join
each decision to candidate/abstract-instance records, installation results and a
subsequent solver-check event. Existing UNSAT records alone cannot capture SAT,
UNKNOWN, timeout or an action that generates no usable candidate.

Persistent identities use source quantifier provenance, rule direction,
owning module, alternative/path descriptors and canonical symbolic bindings.
Do not use Egg IDs, addresses, transient operation handles or model equality
representatives as cross-run identity. Keep current training keys untouched in the facade;
introduce stable effort links additively, since existing term decision keys can
contain e-class IDs.

Record returned substitutions separately from newly examined matches because
prefix replay repeats work. Distinguish immediate candidate yield, selected
instances, assertions actually added and eventual solver/proof outcomes. These
are correlated observations, not claims that one action caused a proof. No
learning algorithm or reward function is part of this change. Detailed choice
capture stays opt-in; observation must not invoke additional searches.

An action that supplies the last lemma before UNSAT is immediately decisive in
that accumulated context, not necessarily the best action to perform first.
Record the assertion context and preceding actions/work. An UNSAT core provides
participation evidence; whether a different action order would have succeeded
requires controlled replay or another run. Do not assign all proof credit to
the final instance by default.

## Migration and acceptance

1. Before changing source, preserve the current binary, source snapshot/diff and
   hashes, and capture small deterministic baseline traces. Do not rebuild over
   the only preserved quick binary. Include the untracked quantifier modules.
2. Introduce the policy facade. Route cost construction,
   ranker access, budgets and builder configuration through it; retain existing
   execution order, updating callers to the new API. Explicitly label scheduling delegation as
   incomplete at this checkpoint rather than claiming full policy control.
3. Extract concrete array and quantifier refinement modules under the existing
   `Abstract<F>` adapter. Centralize graph access behind coordinator-owned
   construction/search interfaces and retain shared history. Current dual-graph
   storage may remain only as a temporary migration implementation for this
   initial checkpoint; the target is one graph. Keep baseline interleaving and
   existing shared machinery, and verify instance-selection parity.
4. Extract effort decisions across both modules: separate next-rule selection
   from page execution, and dependency guidance from discovery/request execution.
   Reproduce the state machine above through `DefaultEffort`; add module-aware
   operation dispatch and observation links. The coordinator now follows policy
   decisions instead of embedding the baseline phase order.
5. Replace temporary graph storage with one staged graph, frozen during
   matching. Reconcile vocabulary, typing, provenance and equality construction;
   introduce graph-version invalidation. Check selected-instance parity again.
   This change is not automatically mechanical: surface any changed selections
   and resolve them before claiming equivalence.
6. Move genuinely shared instantiation infrastructure into neutral modules in
   a separate mechanical refactor, updating imports directly.
   Avoid a new term language or cost-interface redesign in that move.
7. After parity, add adaptive allowances and continued search after local budget
   exhaustion as explicit behavior changes, then alternate effort policies and
   ablations. No new Paxos heuristic is bundled with the structural refactors.

The user's first-pass acceptance criterion is instance-selection parity for
array programs and preservation of current distributed-protocol progress.
Compare the ordered selected instances and installed assertions at corresponding
depths/checks on captured cases, not just final outcomes. Use canonical symbolic
forms so model-local IDs do not produce artificial differences. Internal cache
hits, allocation details and timings need not match; broader decision traces
help diagnose deviations rather than creating an additional exact-trace gate.

For unfinished protocol runs, compare their selected-instance prefixes under
controlled work/check cutoffs and completed-depth progress. Preserve the recorded
Paxos baseline honestly: the handoff completed depth 0 and timed out at depth 1;
it did not establish a concrete counterexample or a depth-10 result. Capture any
other available protocol baselines before refactoring rather than inventing
coverage. Identical timeout timestamps or equal work reached in a fixed number
of wall-clock seconds are not required.

Compare ordered decisions, representatives, requests/pages, selected formulas,
installation order, history changes and solver return points on small array,
nested/witness, dependency fairness and signed-alternative fixtures. Compare
symbolic traces where model-local identifiers differ; update record consumers
directly when schemas change. Exercise both rankers, winner limits, learned selection, model
refresh, same-model re-entry, empty-pass reuse, stale operation rejection and
bounded exhaustion. Verify component replacement through its behavior with the
other component configurations held fixed.

Add mixed array/binder cases that require both modules, and assert the sequence
of module operations, newly installed terms and solver checks. Verify that an
instance from one module is visible to the other on refresh, both discard stale
model state, and same-model graph growth invalidates both modules' graph-dependent
state while preserving valid symbolic evaluation caches and scheduling history.
Exercise array-only and binder-only inputs through the same coordinator without
inventing new CLI modes. At the parity checkpoint, preserve existing exhaustion
outcomes. For the continued-search policy, check that local exhaustion leads to
supported further work and external termination remains responsive. Neither
module may turn exhausted search into global proof completion.

Run library tests, Clippy, formatting and diff checks after implementation. The
handoff's 290 passing tests describe its prior validation, not validation newly
performed for this design. Paxos is a smoke/regression case; neither a SAT
abstract model nor a timeout is a concrete counterexample, and a single timing
comparison is not a convergence result.

## Alternatives considered

- **One trait for every decision:** expands the interface to cover unrelated
  term, batch and scheduling state; makes controlled replacement harder.
- **Three independent top-level knobs only:** preserves existing interfaces but
  leaves upstream effort hidden and gives no complete policy identity.
- **A universal scalar cost for terms, paths and effort:** discards operational
  constraints and confuses logical compilation with preference.
- **Rewrite all strategies around a new driver:** expands risk without helping
  the first abstract-array/binder migration.
- **Two independent `ProofStrategy` implementations cooperating directly:**
  duplicates proof lifecycle ownership, model refresh and solver-return decisions;
  use two refinement modules under one coordinator instead.
- **One independently owned graph per refinement module as the target:** rejected
  during review; use one coordinator-owned graph and separate module search state.
- **Unrestricted shared mutation during matching:** unnecessary and invalidates
  active enumeration; allow coordinator construction only between search rounds.
- **Full theory-plugin framework immediately:** adds generality beyond the two
  demonstrated work sources; begin with concrete modules and typed dispatch.
- **Coordinator-enforced fairness or heuristic phase gating:** hides effort
  choices from ablations; both belong to replaceable effort policies.

The composed policy controls cooperation between two identifiable refinement
modules over one staged graph, retaining shared instantiation machinery and
existing component seams.
One coordinator owns their interaction with the proof loop, and one policy
configuration concentrates effort choices, reproducibility and observation.
