# Cubicle and MCMT translation semantics

Local-source audit, 2026-10-31. Scope: the imported corpus under
`examples/quantified-transition-systems`; this note does not change any source model.

## Sources and confidence

The authoritative sources inspected were:

- **C**: `/tmp/yardbird-bulk-cubicle.tar.gz`, archive root
  `cubicle-905fda77153f3cb18c8d6ef99c3eabba5738824a/`.
  Grammar: `parser.mly`; elaboration: `ptree.ml`; type checks and initialization:
  `typing.ml`; update semantics: `pre.ml`, `forward.ml`; process substitutions:
  `variable.ml`; safety assumptions: `prover.ml`; base sorts:
  `smt/alt_ergo.ml`, `smt/z3wrapper_actual.ml`.
- **L**: `/tmp/yardbird-cade21-lambda.tar.gz`, archive root `cade21-lambda/`.
  Frontend: `lambda/_mcmtparser.py`; interpretation and proof export:
  `lambda/_lambda.py`. The archive digest recorded by the import is
  `1aba176ea6cf6ae6fbf92c5320cebe5a8def6043b483a0ddb252118d76d714a4`.

L is a primary source for **Lambda's MCMT interpretation**, not a complete MCMT
language specification. Its intentional simplifications must not silently become
claims about every historical MCMT dialect. The imported alternate `.mcmt` dialect
and four older `.in` files exceed L's parser.

## Corpus inventory

Counts inspect all imported files, stripping Cubicle `(* ... *)` comments for
keyword counts and anchoring MCMT directives at line starts.

| Feature | Files | Occurrences where useful |
|---|---:|---:|
| Cubicle `.cub` | 171 | 128 Cubicle + 43 Lambda |
| `forall_other` | 145 | 511 |
| `invariant` | 11 | 40 |
| `const` | 13 | 13 |
| nondeterministic scalar assignment `:= .` / `:= ?` | 16 | |
| multidimensional arrays | 19 | |
| uninterpreted `type T` | 32 | |
| `real` | 10 | 41 |
| `predicate` | 1 | 2 |
| ordinary `forall` | 1 | 1 |
| `number_procs` / literal process IDs | 1 | `peterson_two_proc.cub` |
| `let`, `exists`, `exists_other` | 0 | 0 |
| MCMT `.in` | 116 | 99 Lambda + 17 Cubicle |
| alternate `.mcmt` | 1 | `cubicle/examples/mcmt/flash.ctc.mcmt` |
| `.in` with `:global` | 94 | 617 declarations |
| `.in` with `:local` | 116 | 997 declarations |
| `.in` with `:system_axiom` | 14 | 16 |
| `.in` with `:uguard` | 51 | 234 |
| `.in` with subrange types | 43 | |
| semantic `:comment index_arrays` | 23 | |
| semantic `:comment index_arrays_extra` | 13 | |
| `.in` with `:u_cnj` | 4 | 7 |
| `.in` with `:map_back` | 2 | 49 |
| suggested-negated-invariant block | 1 | |

There are 3,406 `.in` transitions, 7,722 cases, and 179,362 value assignments.
Every `.in` has one initial block; 113 have one explicit `:unsafe` block. The three
without it use older `:u_cnj` notation. Raw substring searches misleadingly count
commented-out `:unsafe` examples as additional properties.

## Cubicle lowering rules

1. **State and sorts.** `var V : T` is scalar state; `const C : T` is immutable;
   `array A[proc,...] : T` is a total function with the listed process indices.
   A declared enumeration is exhaustive and constructors are distinct. A bare
   `type T` is uninterpreted. Boolean source constructors can map to SMT Bool.
   `int`/`real` are arithmetic sorts. Sources: C `parser.mly:201-247`,
   `smt/alt_ergo.ml:54-85`, `smt/z3wrapper_actual.ml:71-106`.
2. **Init versus bad states.** `init (x y) { F }` universally quantifies all
   combinations of indices, including `x=y`. `unsafe (x y) { B }` denotes an
   existential bad state with distinct witnesses; safety is
   `forall x,y. distinct(x,y) => not B`. Multiple unsafe declarations are separate
   bad alternatives, so combine their negations in the property. Sources:
   C `ptree.ml:482-490,596-628`, `typing.ml:385-443`,
   `variable.ml:103-119,145-153`, `prover.ml:33-42,173-181`.
3. **Invariant polarity.** An `invariant (x y) { B }` also supplies a forbidden
   cube, **not** the assertion `B`. C elaborates it with `unsafes_of_formula`;
   `prover.ml:169-171` negates each instance before using it as an assumption in
   initial-state safety checks. A converter should explicitly classify these as
   supplied proof hints, preserve them in audit metadata, and decide whether to
   check them separately. Assuming their positive bodies is wrong. Silently
   promoting unverified hints to transition axioms changes the system.
4. **Actions.** Action parameters are pairwise distinct existential process
   witnesses. `forall_other j. G` means
   `forall j. (and j!=param_1 ... j!=param_n) => G`, excluding **all** action
   parameters. General `forall j. G` includes parameters as well; C rewrites the
   single-binder form into `forall_other` plus instances at all parameters.
   Sources: C `forward.ml:511-518,579-600`, `ptree.ml:492-519`.
5. **Simultaneous assignments.** All RHS terms and case guards use the pre-state.
   Untouched scalars/arrays are framed. `V := .` and `V := ?` leave next V free,
   with its declared type; they do not make other assignments read next V.
   Sources: C `parser.mly` assignment productions; `pre.ml:91-165`,
   `forward.ml:455-509`.
6. **Point writes versus comprehensions.** `A[x,y] := t` preserves every other
   entry. `A[j,k] := case ...` is a whole-array comprehension binding j,k;
   these names must not shadow action parameters. Cases are ordered ITEs. The
   final branch is unconditionally the default, **even if written with a guard
   instead of `_`**: `forward.ml:455-470` discards its condition. Earlier cases
   have first-match priority. Sources: C `parser.mly` array assignment and
   `swts` productions; `typing.ml:254-274`; `forward.ml:455-509`.
7. **Macros and explicit quantifiers.** `predicate name(args) { F }` expands by
   argument substitution, accepting formula or term parameters. Respect bound
   variable scope. `forall x <> y. F` and `exists x <> y. F` range over distinct
   process tuples. The corpus uses macros/ordinary quantification only in
   `cubicle/examples/german.ctc_function.cub`; its unsafe property expands
   `not inv1(Invalid,Exclusive)`. Sources: C `parser.mly` expression and
   `lidents_plus_distinct` productions, `ptree.ml:188-305,482-490`.
8. **Process universe.** Upstream SMT wrappers represent individual process
   names as Int, but quantifiers are instantiated over selected process
   representatives, not every integer. Ordinary proc comparisons therefore have
   arithmetic order. Do not assume that replacing every process quantifier by
   `forall ((p Int))` preserves arbitrary finite-process semantics. An ordered
   Proc sort with injective rank into Int preserves comparisons among selected
   representatives; it still needs a documented finite-domain interpretation.
   The one `number_procs 2` input needs exactly two distinct process values #1
   and #2. Sources: C `smt/alt_ergo.ml:69-72`,
   `smt/z3wrapper_actual.ml:92-97`, `variable.ml`, `parser.mly:199-202`,
   `cube.ml:82,100`, and imported `peterson_two_proc.cub`.

No Cubicle `axiom` declaration appears in this grammar. Do not conflate invariants
with axioms. `let` appears in the grammar but not the imported corpus; its runtime
meaning was not established in this audit and should be rejected until supported.

## Lambda's MCMT interpretation

- `:local A T` is indexed state; `:global G T` is scalar state. A source `G[j]`
  still means G. `:smt (define C :T)` creates a frozen scalar; its next copy must
  equal the current value. `nat` and `int` both become Int, and subrange type
  definitions become Int **without retaining their bounds** in L. If the intended
  target is original MCMT semantics instead, independently validate nat/subrange
  restrictions; silently adding bounds is not an exact reproduction of L.
  Sources: L `_mcmtparser.py:115-122,200-253,396-404`.
- Init universally quantifies its `:var` names with no distinctness. Unsafe
  negation universally quantifies with `Alldiff(vars) => not(cnj)`.
  `:system_axiom` universally quantifies its conjunction. Axioms must hold in
  init and on current/next transition states. Sources:
  L `_mcmtparser.py:268-305,406-414`, `p_system_axiom`;
  `_lambda.py:815-816,868-880`.
- Transition `j` is the universally quantified update index. Other declared
  variables are existential parameters. **No implicit pairwise distinctness**
  is added to these parameters by L; unlike unsafe, there is no `Alldiff` here.
  The TS container is a namedtuple, not a hidden elaboration stage.
  Sources: L `_mcmtparser.py:416-454`, `_lambda.py:259-260`.
- Repeated `:uguard` lines are a **disjunction** of conjunctions. If x exists,
  the universal guard excludes j=x. It does not automatically exclude every
  existential parameter. Local-guard reads indexed by non-bound terms are
  flattened using existential index witnesses. Sources:
  L `_mcmtparser.py:460-510`.
- Case semantics are a specialized frontend convention, not Cubicle ITEs.
  If x exists, the first case sets every next-state value at x (and every global)
  after substituting j=x, **ignoring the written first-case condition**. If no x
  exists, it is instead a universally guarded update. If the first subsequent
  case is syntactically `y=j` and y exists, it similarly sets values at y.
  Remaining cases produce universally quantified implications, additionally
  guarded by j!=x when x exists. Overlapping remaining conditions impose all
  corresponding equalities. Uncovered indices are unconstrained. Each case has
  one `:val` per local/global declaration in declaration order; values all read
  the pre-state. Sources: L `_mcmtparser.py:542-618`.
- `:comment index_arrays ...` and `:comment index_arrays_extra A ...` are semantic
  directives, despite looking like comments. They add range/domain axioms for
  pointer-valued arrays, optionally permitting sentinel integers. With extras,
  local-array axioms also require nonnegative process indices. Dropping these
  changes the model. Sources: L `_mcmtparser.py:51-63,159-193`.
- L internally represents index witnesses by Int variables, but its proof dump
  explicitly introduces an uninterpreted `[index]` sort plus injective
  `index2int`. **Quantifying all mathematical integers is not equivalent**:
  `index_arrays_extra` can give `forall j. j>=0`, which becomes inconsistent if
  j ranges over all Int. A source-preserving converter must separate process
  witnesses from integer data and apply this injection to arithmetic comparisons
  and pointer equalities. Sources: L `_lambda.py:180-186,819-856`.

## Explicit unsupported cases and audit priorities

Older MCMT files needing a separate grammar/semantics decision:

- `cubicle/examples/mcmt/german_cub_data.in`: `:u_cnj` in addition to unsafe.
- `cubicle/examples/mcmt/szymanski_na.in`: `:u_cnj`, suggested-negated-invariant
  block, and no `:unsafe`; some suggested formulas are malformed.
- `cubicle/examples/mcmt/flash.ctc.in` and `crash.in`: `:u_cnj`, `:map_back`, no
  `:unsafe`.
- `cubicle/examples/mcmt/flash.ctc.mcmt`: alternate syntax such as
  `define-type T (:mcmt (subrange 1 3) :)` and `global nat Home [nat]`.

Reject unsupported constructs with a per-source manifest entry rather than
silently dropping properties. For supported outputs, highest-value audit checks
are: nonempty initial state; enum exhaustiveness; property polarity/distinctness;
frame conditions and simultaneous updates; Cubicle final-case behavior; MCMT
local/global declaration ordering; index-domain axioms; and bounded differential
checks of both safe and deliberately unsafe small models. A parser success alone
does not validate translation semantics.
