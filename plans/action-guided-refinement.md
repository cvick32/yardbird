# Action-guided refinement

## Implemented foundation

`transition_index.rs` owns the shared static traversal of VMT transition control
structure. Array dataflow consumes its guarded state updates rather than walking
the transition formula independently. The index retains:

- Named actions and their complete Boolean requirements, including alternatives.
- State updates indexed by target variable and associated with an action.
- Path guards and both branches of conditional update expressions.
- Occurrences of lowered binder helpers, including capture arguments and paths
  within action requirements; helper names resolve to the existing binder plan.
- Definition and frame information for indexing source terms at a concrete BMC
  transition frame.

Distributed-protocol action flags are mutually exclusive. Runtime selection is
specific to one solver model and transition frame; observing two true flags is
an encoding-contract error. No flags is allowed for actionless/stuttering cases.
The index does not assert exclusivity or any other new formula.

Array-specific expression roles remain in `theories/array/array_dataflow.rs`.
That module attaches read/write sites to action requirements and update paths.
Its existing property traversal now uses the shared action index. A second
entry point accepts ground, already-framed terms from property witnesses,
preserving mixed-frame captures while following enabled actions and branches.

The index is built after binder lowering and array encoding for protocol models,
even when profiling and the cone policy are disabled. It also supports existing
actionless array programs. Quantified updates expressed as binder constraints
remain part of the action requirements; they are not misclassified as direct
assignments.

## Connected refinement

The abstract coordinator now keeps `RefinementObligations` across solver models
at a fixed BMC depth. Its dependency-discovery operation:

1. Explains the negated property and enabled action requirements with Boolean
   polarity and model-selected branches. False universals and true existentials
   supply their existing Skolem witnesses, including the original captures.
2. Sends demanded reads through indexed state updates. Array reasoning emits
   globally valid same-index, different-index, and constant-array instances.
   Both write-index cases contribute symbolic alternatives; opaque functions
   such as witnesses are never rewritten while following state updates.
3. Passes signed predecessor demands to the existing binder dependency search,
   which performs structural, typed unification. Fully bound links become exact
   binder instances without enumerating a Cartesian product.
4. Retains every discovered instance, including currently satisfied links.
   Each new model reevaluates them, offers violated instances to the ordinary
   cost/ranking policy, and installs selected candidates through the existing
   normalization, deduplication, and replay machinery.

Model evaluation caches remain local. Persistent work contains only symbolic
terms, rule identity, and substitutions. The pool resets at a new property
check depth; installation handles replay of previously installed schemas.
Source updates and model equalities are search hints, never extra axioms.
The ordinary dependency and theory searches remain the fallback, including the
existing periodic scheduling escape from dependency search.

This path is enabled for named-action protocols whose lowered plan contains
binders and no remaining lambda rules. Actionless and SMT-LIB inputs retain
their existing dependency path. Lambda helper equations still use the existing
matcher, because structural transport does not follow those equations yet.
Constant lambdas eliminated into constant arrays do not require that fallback.
The producer index still handles unconditional universal conclusions;
conditional producers, partially bound directed links, and relational updates
can require the ordinary matcher. There is no claim of complete directed
closure for those fragments.

## Validation

A checked-in frozen fully abstract Paxos frame-1 query isolates agreement while
leaving action choices available. The automatic test supplies no instance list
or binder-ID hints to discovery. It closes in seven model rounds with nine array
instances and twelve binder instances. It also checks that a link which was
previously satisfied is retained and later used when violated. This certificate
is sufficient, not asserted to be minimal.

Focused tests check Boolean branch relevance, unchanged witness captures through
conditional updates, and validity of each emitted array axiom against native Z3
arrays. The existing static index coverage includes Paxos, distributed lock,
two-phase commit, and ring leader election.

Library validation: 339 tests passed, with the existing learned-policy test
skipped because `tests/fixtures/policy_parity/learned-model.json` is absent.
The focused integration suite passed 23 tests. The optimized broad protocol
suite passed five tests and timed out in two: fast Paxos at frame 0 and
synchronous lock server at frame 4. Profiling confirms that neither timeout
exercises the connected pass: fast Paxos retains a lambda rule and synchronous
lock server has no remaining binders. Short controls with the prior release
binary also time out at those frames. The full suite is not claimed green.

Runtime measurements and integration-test results are recorded in
`.scratch/action-guided-refinement/analysis.md`.


## Resumable obligation agenda

Directed discovery now retains unfinished work in `refinement_obligations/agenda.rs`.
It rotates through Boolean explanation, array transport, quantified equations,
clause joins, backward dependencies, and source-helper admission. Each newly
exposed atom or helper wakes the applicable operations. New ground instances
wake signed body subscriptions (true universals and false existentials).
Clause joins retain partial substitutions; dependency paths can resume when a
previously unavailable root is discovered. The connected agenda has no fixed
64-demand or eight-link truncation. Policy bounds each slice and the consecutive
slice burst, allowing ordinary matching and the driver's timeout checks to run.
Equation compilation retains a sibling/body cursor and charges each visited
source node. Equation matching retains its position in both the goal tree and
the same-head equation list, charging each attempted equation or traversal step.
Failed matches and subtrees without equations also consume work. Completed roots
are matched against existing goals; later goals see all completed roots. The
array-transport operation still performs its inner traversal as one work unit;
it has not yet received the same finer-grained accounting.

Search contexts log the model evaluations that selected their branches. A new
model can reactivate a context only after all logged decisions are rechecked;
incompatible contexts remain dormant. No e-class IDs or unchecked model values
cross this boundary. Valid guarded instances are pooled independently and
reevaluated for candidate selection. Contexts and the symbolic pool reset at a
new BMC depth; installed schemas continue through ordinary replay.

The retained-instance pool caches normalization and lazily prepared expressions
and provenance for the current problem/depth. Model evaluations are cached by
the current model identity. Satisfied entries leave the active scan until that
identity changes; new entries are processed incrementally. Pending and installed
keys are checked on every offer, and costs, ranking, and winner allowances are
recomputed. Failed evaluations propagate without dropping unfinished entries.

A fixed-model regression compares 4096 work units delivered together with
one-unit slices and model revalidation between slices. Further tests cover
changed-decision rejection, late frontier/root arrivals, dependency chains of
1, 2, 4, 8, and 16 links, and bounded scheduling bursts. The three frozen Paxos
queries remain regression tests. Continuation is a search-lifecycle guarantee,
not a completeness claim: the available inference operations can still reach
quiescence before finding a refutation. See `.scratch/paxos-depth4/` for live
measurements and the remaining deeper-Paxos limitation.

## Binder-body connections

`theories/quantifiers/body_matching.rs` connects obligations through scoped
binder bodies. It expands lowered helper definitions, compares bound variables
by scope position, normalizes implication/disjunction, and checks ground capture
equalities only as model-local search hints. A false existential can obtain its
ordinary tuple from an available universal with a matching body. The emitted
instance preserves the existential's original captures.

Active universal guards also drive signed structural joins against existential
witness bodies. Fully bound capture tuples request the original witness lemma;
the corresponding helper prerequisite is sent through ordinary backward search.
This connects, for example, a universally quantified membership guard to a
background non-emptiness/intersection witness without naming a protocol, frame,
sort, action, or chosen tuple. Partial joins and every compatible alternative
stay in the agenda. Bound variables inside a source binder cannot become ground
captures. No source/body equivalence or model equality is asserted as a lemma.

These are inference preferences, not a complete quantified theorem prover.
Witness-body conjunctions are matched against clauses from an active universal;
other Boolean shapes and tuples requiring other joins retain the general
matcher fallback. Tests cover source/target binder renaming, scope, repeated
variables, sorts, original captures, join continuation, and the handoff to a
background prerequisite. Two reduced fully abstract Paxos regressions preserve
source constraints and fixed action paths, with all learned instances removed.

Investigation, standalone ground certificates, timing controls, and remaining
limits are documented in `.scratch/paxos-frame3/results.md`.
