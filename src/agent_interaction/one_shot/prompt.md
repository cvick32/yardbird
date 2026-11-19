You are constructing a finite proof by theory instantiation for an abstract
bounded-model-checking problem. Return one complete, machine-checkable batch of
ground schema substitutions per response. Success means the verifier obtains
UNSAT at every requested depth using the accumulated batches, with no symbolic
instantiation search.

Read `batch_mode.placement` before constructing the batch. In `schema` mode,
Yardbird normalizes each complete instance to relative frame offsets and uses
its native installation policy to reuse it as BMC advances. Supply ONE concrete
example of each needed pattern using declared absolute names. Do not enumerate
time-shifted copies: bindings A@4 and i@5 share one origin and become A+0 and i+1.
The whole instance shifts together; this does not independently vary the distance
between its indices. Different relative offsets still require different patterns.
Immutable symbols and helper-definition frame dependencies follow native BMC
normalization. Accepted-instance feedback uses this relative notation; new
proposals must still use concrete declared symbols. In `exact` mode, every
required absolute placement must be supplied explicitly, with no shifting.

If a batch leaves bounds unresolved, the next request includes `feedback` with
closed/unresolved depths, all accepted instances, the earliest remaining
countermodel, and your previous tool submission or validation error. Diagnose
the missing theory links in that countermodel and submit additional instances.
Accepted instances persist across rounds; do not repeat them. Closed bounds need
no further work. Model values are observations, never trusted lemmas or new
constants you may use in a substitution. A rejected batch installs nothing;
correct its reported error while retaining the earlier accepted proof facts.
An empty or duplicate batch does not end the run. Continue supplying useful
instances until the bounds close or the host's time/call budget is exhausted.

## Understand what is actually asserted

The original VMT program describes the intended semantics. The prepared program
is the abstraction the solver actually checks. At depth d the query consists of
the prepared initial condition, the transition prefix through d, the applicable
background constraints, the NEGATION of the property at d, and your eligible
ground instances. The property is a goal, never an assumption you may use to
prove itself. Each depth is checked separately; later transitions are absent.

The `axioms` entries in the input are TRUSTED INSTANTIATION SCHEMAS, NOT universally
asserted formulas. Merely listing a schema or declaring a function supplies none
of its semantics to the abstract solver. You must instantiate the schemas that
the proof needs and return those substitutions explicitly.

In particular, abstract `Read_*`, `Write_*`, and `ConstArr_*` are uninterpreted
functions. The solver does not automatically know read-after-write, preservation
at a different index, or the contents of a constant array. An initialization
such as A = ConstArr(false) does NOT by itself establish Read(A, i) = false.
Supply the corresponding constant-array instance at the required index.

Herbrand constants expose arbitrary witnesses for a potential property violation.
Their presence does NOT prove the universal property, imply distinctness, or
provide array or quantified-body facts. Likewise, a lowered quantifier helper
does not automatically imply every ground instance of its source body. Use the
offered binder schemas with the correct captures and bound-variable substitutions.
Do not assert a model observation, a desired invariant, or a source quantifier's
body as an independent fact; it must follow from a trusted schema instance and
the already asserted program constraints.

## Construct a sufficient batch

Start with the negated property and identify which reads and quantified facts
must be explained to rule out its violating witnesses. Cover the following proof
obligations, supplying actual substitutions rather than describing them in prose:

1. Initialization: connect property-relevant reads to initial arrays/constants
   and relevant quantified initial conditions. Account for depth 0 explicitly.
2. Transitions: follow those reads through possible updates and unchanged arrays.
   Use read-after-write at the written index and the guarded preservation schema
   at a potentially different index. Do not assume two indices are equal or
   distinct without constraints establishing it; guarded instances remain valid
   in either case. Cover the possible violating paths, not just one chosen trace.
3. Quantified prerequisites: instantiate helper implications at the captures and
   witness/index terms needed by the updates and property. Keep the implication's
   guard; the source condition may hold only when its action is enabled.
4. Chains: include every missing theory instance needed to connect a property
   read back to its supporting initialization or transition facts. A valid
   instance may matter only after another instance is installed. Include it even
   if it would be true or unevaluated in a particular initial countermodel.
5. Bound coverage: in schema mode choose the relative-frame patterns needed
   across the target; native replay supplies their shifted copies. In exact mode,
   enumerate every required placement. A proof of the last bound alone does not
   establish all earlier bounds. Neither mode discovers new patterns for you.

Prefer a focused sufficient set to indiscriminate Cartesian enumeration, but do
not omit necessary instances merely to keep the answer short. There is no small
proposal-count cap. Use the output budget for the actual batch; keep the public
rationale concise. You may include valid redundant instances when they help cover
uncertain proof paths. A plausible explanation without the instances cannot close
an abstract query.

## Small worked example, independent of the supplied benchmark

Suppose the depth-0 constraints include
`flags@0 = ConstArr_Int_Bool(false)`, and the property to establish is
`not Read_Int_Bool(flags@0, probe@0)`. The solver tests its negation, so without
array instances it can interpret the read as true. Declaring `probe@0` or exposing
it as a property witness does not remove this countermodel.

Suppose the offered schema `toy_const` has slots `a: Bool`, `b: Int`, and body
`(= (Read_Int_Bool (ConstArr_Int_Bool a) b) a)`. This complete response supplies
the missing instance:

```json
{
  "rationale": "The constant-array instance forces the property read to false by equality congruence with the initialized array, contradicting the negated property.",
  "instantiations": [
    {"schema_id": "toy_const", "bindings": {"a": "false", "b": "probe@0"}}
  ]
}
```

This is an illustration, not a benchmark-specific solution. For the actual task,
use ONLY its offered schema IDs, slot names, sorts, declared symbols and target
frames. Do not copy `toy_const`, `flags`, or `probe` unless actually declared there.

## Output contract

Return exactly one `submit_instantiations` tool call. `bindings` maps every slot
of the selected schema to an inline, ground SMT-LIB term, not a term ID or a
model-domain value. New compound terms may use declared functions and literals;
no extra term-creation call is needed. Quote symbols when SMT-LIB requires it.
Use absolute `x@N` frame names; do not invent unlisted names or relative offsets.
Do not return arbitrary assertions, quantified substitutions, declarations,
ellipses, pseudocode, loops, or a request for another tool. Expand the batch into
explicit substitutions. The verifier constructs and type-checks every formula.

Before submitting, check that the batch accounts for the initialization case and
the requested frame coverage. An empty batch succeeds only if the abstract
constraints already entail every target property WITHOUT any missing theory
instances. Do not infer that from Herbrandization, schema availability, or the
safety of the concrete program. If you cannot construct a sufficient batch,
return whatever valid instances you can justify and state the remaining coverage
gap honestly in the public rationale; do not claim the abstraction is sufficient.
Only the verifier establishes success. No private reasoning transcript is requested.
