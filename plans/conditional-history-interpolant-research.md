# Conditional History Synthesis: CondHist Findings and Yardbird Final-Leg Plan

Status: primary-source code investigation (August 2026)

> **Checkout update (September 2026):** The historical/parity analysis below was
> written before the current uncommitted semantic-core work. The current checkout
> now represents first- and last-occurrence capture, latch transitions, the
> prophecy/history property constraint, localized-axiom replay, and VMT export in
> `AuxiliarySpec`. The sections titled "Missing or semantically incomplete" and
> "Recommended final implementation leg" remain useful as design history, but
> their semantic-core bullets are superseded by the final addendum, "Capture
> semantics and shared predicate cost." The concrete-validation path now also
> emits one SMTInterpol partition per BMC frame, selects the native-array logic
> from the concrete session, and returns frame-mapped sequence interpolants plus
> a `PredicateCatalog`; trace classification and guard selection remain pending.

## Bottom line

The legacy CondHist implementation does not solve the symbolic synthesis formula
sketched in `countermodel.py`. Its working algorithm is narrower and more practical:
mine atomic predicates from sequence interpolants, test those predicates against the
current abstract counterexample as either a first-occurrence ("safe") or
last-occurrence ("trigger") capture guard, rank the survivors, and install one guard.
The symbolic formula is only a comment, and `ProphecyVariable.get_synthesis_formula`
is unfinished (`tools/condhist/src/countermodel.py:1-18`,
`tools/condhist/src/variable.py:416-425`).

Yardbird already has most of the surrounding machinery: non-local conflict records,
trigger policies, runtime auxiliary-variable installation, SMTInterpol invocation,
and structural interpolant predicate mining. The remaining work is not another
e-graph implementation. It is to close the auxiliary transformation's semantics and
connect concrete-validation interpolants to the pending non-local conflict.

## What CondHist actually does

### End-to-end control flow

1. CondHist first runs IC3IA on the current VMT. Only when IC3IA returns a concrete
   trace does it unroll that exact trace length in Z3; the refinement loop repeats
   IC3IA after every change (`tools/condhist/src/smt_to_vmt.py:67-80`,
   `tools/condhist/src/smt_to_vmt.py:82-110`,
   `tools/condhist/src/smt_to_vmt.py:286-318`).
2. The Z3 model is converted into a lightweight e-graph. Model-active transition
   clauses are tracked separately, terms are grouped by equal model values, and
   axiom matching starts from the property (`tools/condhist/src/egraph.py:14-53`,
   `tools/condhist/src/egraph.py:139-180`).
3. The three array axioms are constant-read, read-after-write, and
   read-over-different-write (`tools/condhist/src/array_axioms.py:15-31`). A matched
   instance whose model value is false becomes a `Violation`; matching records both
   substitutions that depended on model equalities and e-node equalities used along
   the control path (`tools/condhist/src/egraph.py:157-180`,
   `tools/condhist/src/egraph.py:251-281`).
4. A violation is local when it has only frame 0 or spans at most one transition.
   Local instances are rewritten to init/transition syntax and asserted directly.
   Wider frame spans require auxiliary variables
   (`tools/condhist/src/violation.py:86-95`,
   `tools/condhist/src/smt_to_vmt.py:218-246`).
5. For a non-local violation, the highest-framed state-variable leaf (normally an
   index or value) is selected for prophecy. The initial guard is a conjunction of
   the equality needed by the axiom match, equalities recovered from the e-graph
   control path, and the program-counter value at the capture frame
   (`tools/condhist/src/violation.py:97-119`,
   `tools/condhist/src/violation.py:157-208`,
   `tools/condhist/src/violation.py:226-274`).
6. If that axiom-local guard is not true where required on the current trace,
   CondHist switches to an interpolant-selected guard
   (`tools/condhist/src/violation.py:72-84`,
   `tools/condhist/src/smt_to_vmt.py:228-245`).

### The auxiliary-variable transformation

CondHist installs three pieces of state:

- A history variable `H` of the captured scalar's sort.
- An immutable prophecy variable `P`, with transition `P' = P`.
- For first-occurrence capture, a Boolean latch `captureH`, initially false and
  monotone once set (`tools/condhist/src/variable.py:264-291`,
  `tools/condhist/src/variable.py:397-411`).

The default history transition captures the selected current/next program term when
the axiom-local condition is true and the latch has not fired; otherwise it stutters
when the condition is false (`tools/condhist/src/variable.py:294-360`). The violated
axiom is localized by replacing the highest-framed term with `P`, and all remaining
framed symbols are rewritten to current/next variables
(`tools/condhist/src/violation.py:171-190`,
`tools/condhist/src/violation.py:242-255`). Finally, the safety property `Q` becomes
`P = H => Q` (`tools/condhist/src/smt_to_vmt.py:266-281`). This property coupling is
the reason the arbitrary immutable prophecy value can stand for the value captured
from the relevant historical frame.

CondHist supports two interpolant capture modes:

- **Safe / first occurrence:** capture under `guard && !captureH`; preserve the
  monotone latch (`tools/condhist/src/variable.py:368-380`).
- **Trigger / last occurrence:** capture whenever `guard` holds and remove the latch;
  the candidate has been checked not to recur after the target frame
  (`tools/condhist/src/variable.py:382-394`).

### How interpolants become guards

For every stored countermodel, CondHist asks its first violation for sequence
interpolants and unions the resulting predicate sets
(`tools/condhist/src/countermodel.py:32-33`,
`tools/condhist/src/smt_to_vmt.py:248-264`). The interpolation problem:

- uses SMTInterpol with `QF_ALIA` and proof/interpolation options;
- declares concrete native arrays by rewriting the abstract `Arr` sort;
- creates one named conjunction per BMC step;
- puts concrete initial facts in frame 0, transition facts in intermediate frames,
  and the failing property path in the final frame; and
- rewrites abstract `Write`/`Read` back to native `store`/`select`
  (`tools/condhist/src/violation.py:444-501`,
  `tools/condhist/src/violation.py:503-569`,
  `tools/condhist/src/violation.py:639-642`).

It keeps interpolants at and after `highest_frame - 1`, translates one- or two-frame
symbols into current/next VMT symbols, recursively mines atomic children, and drops
simple reflexive comparisons (`tools/condhist/src/violation.py:357-404`,
`tools/condhist/src/violation.py:409-442`). This is predicate mining rather than
installing a complete interpolant formula; decomposing `or` and `=>` deliberately
forgets their Boolean structure.

The `Synthesizer` then performs trace classification:

- `safe` candidates include every mined atom plus the negation of its next-state
  shift. They must be false before the target frame and true at the target.
- `trigger` candidates must be true at the target and false afterward.
- Every model test also conjoins the history variable's program-counter guard.
  (`tools/condhist/src/synthesizer.py:5-37`,
  `tools/condhist/src/synthesizer.py:39-49`).

Survivors are ranked by textual overlap with variables, functions, and constants in
the property, with shorter predicates preferred and trigger candidates receiving a
two-times multiplier (`tools/condhist/src/synthesizer.py:79-118`). One top predicate
is installed (`tools/condhist/src/synthesizer.py:51-60`).

The paper-result artifact gives a ready-made regression cohort. For example,
`array_hybr_sum.smt2` used `j >= 0`, while other successful guards include
current-state, next-state, scalar, and array-read predicates
(`tools/condhist/paper-results/CondHist/aeval-multiple-results.py:50-109`).

## Important CondHist assumptions and rough edges

These behaviors are useful evidence, not contracts Yardbird should copy blindly:

- Interpolation effectively assumes a `pc` variable: `Synthesizer` indexes
  `hist.pc_ante[0]`, although `HistoryVariable` permits an empty PC antecedent
  (`tools/condhist/src/synthesizer.py:6-8`,
  `tools/condhist/src/variable.py:333-340`).
- Array interpolation is hard-coded to `Array Int Int` / `QF_ALIA`, so it does not
  cover Yardbird's typed and bit-vector arrays
  (`tools/condhist/src/violation.py:451-470`).
- Interpolants and equality dependencies may contain at most two adjacent frames;
  wider terms raise or degrade to dummy substitutions
  (`tools/condhist/src/violation.py:226-240`,
  `tools/condhist/src/violation.py:332-355`,
  `tools/condhist/src/violation.py:409-429`).
- Only the first violation supplies interpolants, and auxiliary construction returns
  after the first usable equality dependency
  (`tools/condhist/src/countermodel.py:32-33`,
  `tools/condhist/src/violation.py:157-169`).
- Ranking keys are numeric scores in a map, so score ties overwrite candidates;
  the score also uses string containment rather than term structure
  (`tools/condhist/src/synthesizer.py:97-118`).
- Guard candidates are validated only on the current finite counterexample. The
  outer IC3IA/Z3 loop is the eventual semantic backstop, not a proof that the guard
  generalizes (`tools/condhist/src/smt_to_vmt.py:67-80`).

## Yardbird parity map (historical snapshot)

### Already present

- `ArrayConflictRecord` retains the concrete term, frame span, cost, axiom, depth,
  and selection provenance (`src/auxiliary_synthesis/conflict.rs:6-54`).
- `FrameSpan` implements the same initial/transition/non-local distinction without
  counting immutable variables (`src/auxiliary_synthesis/locality.rs:9-49`,
  `src/auxiliary_synthesis/locality.rs:86-98`).
- Trigger modes already include detection, immediate non-local synthesis, budget
  thresholds, and repeated patterns (`src/auxiliary_synthesis/config.rs:4-15`,
  `src/auxiliary_synthesis/trigger.rs:20-121`).
- `AuxiliarySpec` and `VmtBmcSession` can add new variables at all existing frames,
  replay history transitions at existing and future frames, and record the install
  (`src/auxiliary_synthesis/spec.rs:10-42`,
  `src/vmt_bmc_session.rs:546-583`,
  `src/vmt_bmc_session.rs:333-362`,
  `src/vmt_bmc_session.rs:736-797`).
- SMTInterpol invocation and output parsing already return typed `Interpolant`
  values (`src/utils.rs:24-92`). `PredicateCatalog` already resolves `let` aliases,
  mines structurally unique ground atoms, records source interpolant numbers and
  free framed variables, and indexes candidates by variable
  (`src/interpolant.rs:11-37`, `src/interpolant.rs:65-168`,
  `src/interpolant.rs:176-226`).

### Missing or semantically incomplete

1. **The interpolant policy is a label, not behavior.** Any non-`true` policy emits
   a warning and still constructs a true guard
   (`src/strategies/array_abstract.rs:786-809`). `AuxiliarySpec::from_conflict`
   unconditionally sets `capture_guard = true`
   (`src/auxiliary_synthesis/spec.rs:82-110`).
2. **The history/prophecy/property triangle is open.** Yardbird generates
   `H' = ite(guard, captured_term, H)` and `P' = P`, but `property_constraint` is
   `None`; session installation never consumes that field
   (`src/auxiliary_synthesis/spec.rs:113-180`,
   `src/vmt_bmc_session.rs:546-580`). Without `P = H => Q`, the history variable is
   not connected to the checked property.
3. **There is no first-occurrence mode.** The current transition always overwrites
   on every true guard; it has neither CondHist's capture latch nor a last-occurrence
   trace check (`src/auxiliary_synthesis/spec.rs:149-165`).
4. **The localized axiom is depth-specific rather than a reusable symbolic
   transition formula.** `from_conflict` replaces one maximum-frame symbol but does
   not normalize all remaining frames to current/next syntax
   (`src/auxiliary_synthesis/spec.rs:95-110`,
   `src/auxiliary_synthesis/spec.rs:305-367`). The session asserts the result once at
   a selected concrete depth (`src/vmt_bmc_session.rs:799-820`). Because the new
   prophecy symbol is unframed while `localized_frame_span` is computed, the record
   can also report a local span even though installation later indexes the prophecy
   at the selected depth and leaves older absolute-frame symbols untouched.
5. **Interpolants are generated at the wrong lifecycle seam.** The interpolation
   extension runs only after an UNSAT abstract check and only logs terms
   (`src/strategies/interpolate.rs:11-37`). The useful CondHist-equivalent source is
   Yardbird's UNSAT *concrete validation* of a SAT abstract counterexample. The driver
   already retains that concrete `VmtBmcSession`, but immediately calls `strat.sat`
   again without exposing the session or interpolants
   (`src/driver.rs:664-700`, `src/driver.rs:829-852`).
6. **The concrete interpolation dialect is not ready.** `to_smtinterpol` serializes
   the session, but interpolation options are fixed to `QF_UFLIA`
   (`src/vmt_bmc_session.rs:469-518`,
   `smt2parser/src/vmt/smtinterpol_utils.rs:1-6`). Native-array concrete validation
   needs a logic derived from the problem, as CondHist used `QF_ALIA`.
7. **There is no installed-proof export path.** The result model receives ordinary
   instantiations, while auxiliary records are only reported as metadata
   (`src/strategies/array_abstract.rs:555-588`). To run IC3IA on the synthesized
   system, variables, transitions, the localized axiom, and the transformed property
   must also be reflected in the returned `VMTModel`.
8. **Validation is pending, but the source refinement is already suppressed.** The
   record says semantic monotonicity has not been checked
   (`src/auxiliary_synthesis/spec.rs:103-111`), while the array strategy marks the
   source term as auxiliary-covered and skips its ordinary instantiation
   (`src/strategies/array_abstract.rs:498-507`,
   `src/strategies/array_abstract.rs:798-809`). Suppression should be gated on a
   validated, fully installed transformation.

### Read-only runtime confirmation

The current checkout reproduces these gaps on
`examples/array/array_init_increm_two_arrs_const.vmt` at depth 6. Detect mode finds
the non-local conflict
`(=> (not (= i@5 i@1)) ... )` with frame span `{1, 5}`. Running with
`--synthesis-trigger non-local --synthesis-guard-policy interpolant` logs that the
policy is unimplemented, installs `capture_guard: "true"`, records the localized
span as `{1}`, and reports `non_monotonicity_check.status: "pending"` while skipping
the source instantiation. The run completes, but that is evidence that plumbing
works, not that conditional synthesis is semantically complete.

## Recommended final implementation leg (historical snapshot)

### 1. Close the transformation semantics first

Make `AuxiliarySpec` represent the full transformation, not only solver assertions:

- add a capture mode (`FirstOccurrence` with a Boolean latch, or `LastOccurrence`);
- produce `P = H => Q` from the original property and actually install it as the
  active property;
- normalize the localized axiom to a current/next formula using Yardbird's existing
  frame-rewriting machinery, and install it at every applicable BMC frame;
- add the same variables, init, transitions, localized axiom, and property rewrite
  to the output `VMTModel`; and
- replace `Pending` with an actual validation result before allowing the spec to
  suppress the source conflict.

Do not silently fall back from `--synthesis-guard-policy interpolant` to `true`. If no
validated predicate exists, keep ordinary array refinement or report a structured
"no guard" decision.

### 2. Split a pending conflict from an installable spec

Today `Abstract::handle_aux_synthesis_detection` immediately creates a true-guard
spec. Change it to publish an `AuxiliarySynthesisCandidate` containing the selected
`ArrayConflictRecord` and capture target. The driver should synchronously coordinate
the expensive cross-theory step:

1. validate the abstract counterexample with the concrete array session;
2. return a real counterexample if the concrete check is SAT;
3. if it is UNSAT, obtain sequence interpolants from that concrete session; and
4. hand the interpolants plus the still-live abstract model to an auxiliary synthesis
   service, which either returns a complete `AuxiliarySpec` or declines.

This preserves the driver's ownership of concrete validation and avoids teaching the
array strategy how to construct a second solver session.

A small synchronous handoff is preferable to another strategy downcast:

```text
Array strategy --AuxiliarySynthesisCandidate--> driver/interpolation service
Array strategy <--successful AuxiliarySpec------- driver/interpolation service
```

The driver handles a concrete counterexample, no candidate, and interpolation errors
directly. Only a successful spec returns to the strategy. In every non-installed
case, ordinary ground refinement remains available.

### 3. Make interpolation frame-aware

Refactor interpolation serialization to group assertions by BMC frame and carry an
explicit `partition -> frame` map. Select the SMTInterpol logic from the concrete
problem's sorts/theory instead of the fixed constant. Return an artifact such as:

```text
SequenceInterpolants {
  depth,
  partitions: [{ frame, interpolant }],
  predicates: PredicateCatalog,
}
```

Keep `PredicateCatalog` as the candidate producer. Restrict the first version to
ground, quantifier-free predicates that can be normalized to one current frame or one
current/next transition. Retain complete Boolean structure in the raw artifact even
if parity mode initially ranks only atoms.

### 4. Port trace classification, but use structural ranking

For the selected conflict target frame, evaluate candidates in the abstract model:

- **first occurrence:** false on all earlier eligible frames, true at the target;
- **last occurrence:** true at the target, false on all later frames;
- conjoin a PC/control-path predicate only when one exists; do not assume a `pc`
  symbol; and
- also consider a negated next-state shift for first-occurrence candidates, matching
  CondHist's useful `Not(..._next...)` guards.

Rank survivors deterministically with term structure: exact captured-variable/frame
match, conflict/control-path variable overlap, property overlap, smaller AST, then
stable textual order. Do not use scores as unique map keys. Record all rejection
reasons and the chosen capture mode in `AuxiliaryRecord`.

### 5. Validate in layers

Unit tests should cover interpolation partition/frame mapping, native-array logic,
candidate normalization, first/last occurrence classification, optional PC guards,
capture-latch transitions, property coupling, localized-axiom generalization, future
frame installation, and VMT export.

For integration tests, start with the recorded interpolant-dependent cohort in
`tools/condhist/paper-results/CondHist/aeval-multiple-results.py`, especially:

- `array_hybr_sum.smt2` (simple scalar guard);
- `array_init_increm.smt2` (next-state array-read guard);
- `array_init_increm_twice.smt2` (multiple auxiliaries and both polarities);
- `array_init_both_ends_multiple_sum.smt2` (multiple guards); and
- one benchmark that needs no interpolant, to ensure ordinary refinement is
  unchanged.

Acceptance should require: no true-guard fallback under interpolant policy; at least
one selected predicate whose trace classification is recorded; the synthesized VMT
accepted by IC3IA; concrete replay of any reported counterexample; and identical
behavior with synthesis disabled.

## Reviewable patch order

1. **Semantic core and safety rail.** Add explicit first/last capture modes, the
   first-occurrence latch, property coupling, and a real localizer; replay localized
   axioms at every existing/future frame. Keep the source ground instance until a
   post-index locality/coverage check succeeds.
2. **Synchronous synthesis seam.** Introduce `AuxiliarySynthesisCandidate`, so the
   driver can use the concrete model while the abstract SAT model and conflict are
   still from the same refinement epoch, then queue only a successful spec.
3. **Frame-aware concrete interpolation.** Partition the native-array trace by BMC
   frame, select an appropriate logic, retain the partition/frame map, and return raw
   sequence interpolants plus the existing `PredicateCatalog`.
4. **CondHist-parity selector.** Implement first/last trace classification, optional
   PC/control-path conjunction, negated next-shift candidates, deterministic
   structural ranking, accumulated normalized candidates, and complete rejection
   provenance. Remove the silent interpolant-to-true fallback.
5. **Proof artifact and cohort gate.** Reconstruct the synthesized VMT, run IC3IA,
   and compare the recorded CondHist cohort against synthesis-off and ordinary
   refinement baselines. Treat non-`Int` arrays as explicit unsupported cases until
   the concrete interpolation dialect handles their sorts.

## Capture semantics and shared predicate cost

This addendum records the rationale behind CondHist's two capture modes and a
concrete way to let Yardbird's selected cost function rank interpolant predicates.
It describes the current working tree, including uncommitted semantic-core work;
it does not claim that interpolant guard selection is already connected end to end.

### The history/prophecy triangle

History and prophecy solve different halves of the same non-locality problem.
Suppose an array axiom violation mentions a scalar value `t@j` from a distant frame.
A history variable remembers a program value along the forward execution; a
prophecy variable gives the localized axiom a time-invariant name for a value that
will matter at the end. The property connects them.

The paper defines the two refinements separately:

- `HistRef(H, g, t)` adds `H' = ite(g, t, H)`. Under the paper's overwrite
  semantics, terminal `H` is the value of `t` at the **last** transition where `g`
  holds.
- `ProphRef(P, H)` makes `P` a background (time-invariant) value and changes safety
  from `Q` to `P = H => Q`.

These are semantic refinements, not assumptions about the original program. Any
original trace can be extended with the fresh history state, and an original
counterexample can choose the immutable prophecy value equal to terminal history,
making the new antecedent true. See [the paper, Section 4, PDF page
7](../tools/condhist/paper.pdf) ("Prophecy refinement" and "History Refinement").

The legacy code implements the same triangle. `HistoryVariable` constructs the
conditional update, `ProphecyVariable` stutters and exposes `P = H`, the violated
axiom replaces the distant expression with `P`, and each new prophecy wraps the
current property in `P = H => ...`
([`variable.py:328-360`](../tools/condhist/src/variable.py#L328),
[`variable.py:397-411`](../tools/condhist/src/variable.py#L397),
[`violation.py:171-208`](../tools/condhist/src/violation.py#L171),
[`smt_to_vmt.py:266-281`](../tools/condhist/src/smt_to_vmt.py#L266)). The localized
axiom, history transition, prophecy stutter, and property implication therefore
have to travel together; history alone records data but does not make a distant
axiom local, and prophecy alone has no program event against which its prediction
can be checked.

### "Safe" means first occurrence; "trigger" means last occurrence

The paper's formal `HistRef` is last-occurrence capture. The **first-occurrence**
variant is an implementation extension visible in CondHist's `safe` path. The names
are easy to misread: `safe` is not a proof result, and `trigger` here is not the
array-axiom trigger matcher.

For a target transition `j`, after any optional PC/control-path condition has been
conjoined, the two trace classifications are:

| Mode | Candidate must satisfy on this trace | Update | What may happen on the other side of `j` |
|---|---|---|---|
| First occurrence (`safe`) | `not g_i` for every `i < j`, and `g_j` | `C_0 = false`; `C' = C or g`; `H' = ite(g and not C, t, H)` | `g` may remain true or recur after `j`; the latch prevents overwrite |
| Last occurrence (`trigger`) | `g_j`, and `not g_i` for every eligible `i > j` | `H' = ite(g, t, H)` | `g` may have held arbitrarily many times before `j`; later matches are excluded by classification |

CondHist constructs and model-filters exactly those two candidate sets
([`synthesizer.py:5-37`](../tools/condhist/src/synthesizer.py#L5),
[`synthesizer.py:39-49`](../tools/condhist/src/synthesizer.py#L39)). Its capture bit
starts false, becomes/stays true after capture, and freezes history in the safe
transition. The trigger transition removes that bit and overwrites history on each
match
([`variable.py:264-291`](../tools/condhist/src/variable.py#L264),
[`variable.py:368-394`](../tools/condhist/src/variable.py#L368)). Thus both modes
ensure that terminal history contains `t_j`, but for complementary reasons.

This distinction increases expressive power without immediately searching large
Boolean formulas:

- First occurrence handles an **onset**: a simple predicate uniquely identifies the
  target from the prefix even if it stays true afterward. For example, once a phase
  flag turns on, the latch remembers the value at entry rather than repeatedly
  overwriting it throughout the phase.
- Last occurrence handles an **exit/latest event**: a predicate can be common
  throughout the prefix as long as the target is its final match. This naturally
  remembers the last relevant write, loop iteration, or data-flow event.
- A predicate need not be globally unique. With only overwrite capture it would
  have to be absent after the target; with only latch capture it would have to be
  absent before the target. Supporting both accepts any predicate that separates
  the target from either its prefix or its suffix.
- Last occurrence needs no extra Boolean state. First occurrence pays for one latch
  but permits persistent/recurrent post-target guards.

CondHist also expands the first-occurrence pool with `not next(p)` for every mined
atom `p` ([`synthesizer.py:14-17`](../tools/condhist/src/synthesizer.py#L14)). This
is more than ordinary polarity completion: it creates a **falling-edge transition
predicate**. Requiring `not p'` to be false before `j` and true at `j` means that
`p` held through the prefix and first becomes false across the target transition.
That is how a mined state invariant can identify the event where the invariant
stops holding. The paper's motivating example similarly needs the last write that
turns an invariant from true to false, suggesting guards such as
`b[P] >= 0 and not (b'[P] >= 0)`
([the paper, Section 7, PDF page 14](../tools/condhist/paper.pdf)).

The classifications are only witnesses for the current finite counterexample.
They do not prove that the chosen event is first or last on every future trace. The
transformation itself remains a refinement, and CondHist's outer IC3IA/Z3 loop is
the semantic backstop: it reruns verification after installing each auxiliary
construction
([`smt_to_vmt.py:67-80`](../tools/condhist/src/smt_to_vmt.py#L67),
[`smt_to_vmt.py:218-246`](../tools/condhist/src/smt_to_vmt.py#L218)).

### Where candidate predicates come from

CondHist builds a concrete native-array BMC interpolation problem with one named
partition per step, requests sequence interpolants, and keeps the suffix beginning
at `highest_frame - 1`
([`violation.py:357-375`](../tools/condhist/src/violation.py#L357),
[`violation.py:444-501`](../tools/condhist/src/violation.py#L444)). It normalizes a
one-frame predicate to current symbols and a two-adjacent-frame predicate to
current/next symbols; more than two frames is rejected
([`violation.py:409-442`](../tools/condhist/src/violation.py#L409)). It then recursively
splits `and`, `or`, and implication and retains their non-connective children as a
set, dropping only simple reflexive comparisons
([`violation.py:376-404`](../tools/condhist/src/violation.py#L376)). Consequently the
working implementation mines atoms and forgets the interpolant's Boolean structure.

There are two useful differences between the paper and code to remember:

1. The paper says to add each atomic `p` **and `not p`** (Section 7, Figure 8,
   [PDF pages 14-15](../tools/condhist/paper.pdf)). The code begins with the mined
   clauses as-is and adds `not next(p)` only to the safe set; it does not generally
   add `not p` for every atom
   ([`synthesizer.py:8-17`](../tools/condhist/src/synthesizer.py#L8)).
2. Predicate sets are unioned over stored countermodels, but each countermodel asks
   only its first violation for interpolants
   ([`smt_to_vmt.py:260-264`](../tools/condhist/src/smt_to_vmt.py#L260),
   [`countermodel.py:32-33`](../tools/condhist/src/countermodel.py#L32)).

The current Yardbird `PredicateCatalog` is a cleaner representation for the same
raw material. It keeps a standalone parser `Term`, source interpolant numbers, free
base-variable/frame occurrences, structural deduplication, and a variable index;
it resolves only the `let` bindings needed by the atom and rejects quantified or
match-scoped candidates
([`src/interpolant.rs:65-168`](../src/interpolant.rs#L65),
[`src/interpolant.rs:176-226`](../src/interpolant.rs#L176)). That catalog should
remain the semantic source. Ranking does not require putting all predicates in an
e-graph or simplifying whole interpolants.

### Reusing the selected cost function for predicate ranking

CondHist's ranking is bespoke. It gives shorter printed clauses a higher base
score, adds textual bonuses for property variables/functions/constants, multiplies
trigger scores by two, and stores candidates in a map keyed by score
([`synthesizer.py:79-118`](../tools/condhist/src/synthesizer.py#L79)). Besides being
string-based, score ties overwrite each other. The multiplier can also behave
opposite to its "prefer triggers" comment when a base score is negative. This is a
good seam to preserve CondHist's **classification** but replace its **ranking**.

The strong Yardbird story is:

> One heuristic governs both spatial abstraction—which array terms instantiate
> axioms—and temporal abstraction—which predicate/event gets remembered.

That is feasible with a small `auxiliary_synthesis::PredicateRanker<F>` adapter;
the core `YardbirdCostFunction` trait does not need predicate-specific methods.
The existing pieces already line up:

- `YardbirdCostFunction<L>` is an egg `CostFunction` with `u32` cost, and
  `ArrayCostFactory` constructs the selected implementation from the problem
  vocabulary and depth
  ([`src/cost_functions/mod.rs:42-68`](../src/cost_functions/mod.rs#L42),
  [`src/cost_functions/array/mod.rs:30-78`](../src/cost_functions/array/mod.rs#L30)).
- The abstract strategy already creates a fresh `F` with the active
  `ArrayCostContext`, current depth, and `cost_config`, then clones it into term
  extraction and instantiation
  ([`src/strategies/array_abstract.rs:350-419`](../src/strategies/array_abstract.rs#L350)).
- `translate_term(Term) -> Option<ArrayExpr>` already converts supported Boolean,
  arithmetic, typed abstract-array, and `ite` operations directly; unsupported
  applications are preserved as opaque symbol nodes rather than requiring an
  e-graph pass
  ([`src/theories/array/array_axioms.rs:532-755`](../src/theories/array/array_axioms.rs#L532)).
- Existing code evaluates complete expressions with `cost_rec`
  ([`src/training/term_features.rs:95-103`](../src/training/term_features.rs#L95)).

The adapter's pipeline should be:

1. Mine and normalize ground `PredicateCandidate`s.
2. Hard-filter installability/locality and model-classify each candidate as
   first-occurrence, last-occurrence, both, or neither. **Cost must not determine
   semantic eligibility or capture mode.**
3. Build the same `F::from_context(...)` used at that refinement depth.
4. Translate each eligible `candidate.term` to `ArrayExpr` and compute
   `F::cost_rec`. Lower cost wins, matching existing extraction semantics.
5. Break ties deterministically (for example: exact capture-variable/frame match,
   source interpolant/traversal order, then canonical term text). Record the
   semantic class, chosen mode, cost-function name, numeric cost, translation
   status, and tie-break data.
6. If translation returns `None`, use an explicit deterministic fallback such as
   AST size plus canonical text. Never silently discard a semantically viable
   candidate because the array language is narrower than SMT-LIB.

Default guard cost should inherit CLI `--cost-function`, so adding an
`ArrayCostFactory` and wiring its enum/build arm automatically affects both array
term extraction and guard ordering. A later `--guard-cost-function` override could
decouple them for experiments; learned or generated models in particular should
not be silently assumed to generalize to a different candidate distribution. This
is "bring your own" at Yardbird's Rust extension seam, not currently a runtime
plugin ABI: CLI choices are still a closed enum and explicit strategy dispatch
([`src/lib.rs:488-526`](../src/lib.rs#L488),
[`src/lib.rs:651-666`](../src/lib.rs#L651)).

Important caveats belong in the experiment record:

- `ArrayBMCCost` gives framed `pc` a cost of `10000`, prefers property vocabulary,
  and otherwise uses frame distance. CondHist always conjoins its PC condition
  during trace tests, so a mined PC atom and an externally supplied control-path
  constraint should not be conflated
  ([`src/cost_functions/array/symbol_cost.rs:118-146`](../src/cost_functions/array/symbol_cost.rs#L118),
  [`synthesizer.py:5-8`](../tools/condhist/src/synthesizer.py#L5)).
- `AstSize` is immediately meaningful for predicates, while `PreferRead`,
  `PreferWrite`, `PreferConstants`, and specialized split/index-aware costs encode
  intentionally different structural biases. Their scales are not calibrated
  against one another; only ordering within the selected function should matter
  ([`src/cost_functions/array/ast_size.rs:33-41`](../src/cost_functions/array/ast_size.rs#L33),
  [`src/cost_functions/array/prefer_read.rs:33-46`](../src/cost_functions/array/prefer_read.rs#L33)).
- The logistic-regression implementation's raw egg cost is AST size; its learned
  behavior lives in a contextual selector trained for instantiation candidates.
  Reusing raw `cost_rec` does **not** reuse that learned policy, and invoking the
  selector on guards would require guard-specific features/training
  ([`src/cost_functions/array/logistic_regression.rs:69-77`](../src/cost_functions/array/logistic_regression.rs#L69),
  [`src/cost_functions/array/logistic_regression.rs:106-149`](../src/cost_functions/array/logistic_regression.rs#L106)).
- Opaque fallback nodes preserve determinism and totality but hide internal
  structure from a cost function. Record this so benchmark results distinguish
  genuinely structural scoring from fallback scoring.

The desired separation is therefore crisp: interpolants propose events; model
evaluation proves which events capture the required frame on the current trace;
the chosen Yardbird cost function orders only those semantically eligible events;
and the outer CEGAR loop validates the installed transformation.

### Current-checkout correction to the earlier parity map

The current uncommitted semantic-core work has already closed several items that
the earlier snapshot labeled missing:

- `HistoryCaptureMode` now explicitly represents `FirstOccurrence` with latch
  names and `LastOccurrence`
  ([`src/auxiliary_synthesis/spec.rs:14-35`](../src/auxiliary_synthesis/spec.rs#L14)).
- First occurrence now installs `latch' = latch or guard`, captures only under
  `guard and not latch`, and initializes the latch false; last occurrence directly
  uses the guard
  ([`src/auxiliary_synthesis/spec.rs:188-237`](../src/auxiliary_synthesis/spec.rs#L188)).
- `AuxiliarySpec::from_conflict` now produces `P = H` as the property constraint,
  and `apply_to_model` guards the exported property after adding variables, init,
  and transitions
  ([`src/auxiliary_synthesis/spec.rs:137-166`](../src/auxiliary_synthesis/spec.rs#L137),
  [`src/auxiliary_synthesis/spec.rs:270-285`](../src/auxiliary_synthesis/spec.rs#L270)).
- The localized axiom is included in transition terms
  ([`src/auxiliary_synthesis/spec.rs:215-224`](../src/auxiliary_synthesis/spec.rs#L215)).

What remains for the requested story is the interpolant-policy lifecycle and the
selector: classify `PredicateCatalog` candidates against the relevant trace, choose
first versus last as a semantic result, rank survivors through the shared cost
adapter, install the chosen guard/mode, and retain ordinary refinement whenever no
validated guard is available.
