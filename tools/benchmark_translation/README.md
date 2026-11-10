# Offline benchmark translation

This package produces reviewable VMT files under
`examples/quantified-transition-systems/generated-vmt/`. Yardbird itself is
unchanged. Original files and the original import manifest are never rewritten.

From the repository root, with Python 3.10 or newer:

```sh
python3 -m venv /tmp/yardbird-translator
/tmp/yardbird-translator/bin/pip install -r tools/benchmark_translation/requirements.txt
/tmp/yardbird-translator/bin/python -m tools.benchmark_translation
/tmp/yardbird-translator/bin/python -m tools.benchmark_translation --check
/tmp/yardbird-translator/bin/python -m unittest discover -s tests -p test_benchmark_translation.py
```

`--check` verifies byte-identical regeneration and source hashes without writing.
`--only PATH_SUBSTRING` rebuilds a subset without updating the manifest. A full
regeneration refuses to silently retain stale `.vmt` outputs. Unexpected Python
or SMT type errors abort generation; recognized unsupported syntax receives a
manifest entry and no output. The manifest records source/output hashes,
converter hashes, action/property counts, and semantic notes. It does not claim
that every translation has been independently proved equivalent.

The source suffix is retained: `bakery.cub` becomes `bakery.cub.vmt`. An existing
action-dialect `lock_server.vmt` becomes `lock_server.vmt.vmt`. These names avoid
collisions between representations and make the translation input unambiguous.

## Frontends

| Frontend | Generated | Unsupported | Interpretation |
| --- | ---: | ---: | --- |
| Current mypyvy | 124 | 2 | Pinned upstream parser, typechecker, macro expansion, and frame elaboration |
| Cubicle | 162 | 9 | Explicit quantified process witnesses, simultaneous updates and frames |
| MCMT | 111 | 6 | Pinned CADE 2021 Lambda frontend semantics and index-sort proof encoding |
| IvyBench action VMT | 54 | 0 | Complete transition disjunction, derived predicates, globals, frames, per-step auxiliaries |
| Ivy multisig subset | 4 | 0 | Strict Boolean point/slice-update elaboration through mypyvy |
| **Total** | **455** | **17** | |

The 54 existing IvyBench VMT files are the upstream compiler's companions of
54 Ivy and 54 legacy PYV files. Those 108 sources link to the normalized output
in the manifest; they are not counted as 108 additional generated models. This
does not recompile general Ivy or migrate the legacy PYV state convention.

The 17 exceptions are nine legacy Cubicle inputs (`candidate`, older assignment
syntax, or global process array indices), six MCMT dialect extensions (map-back,
old property directives, bare uninterpreted types, or alternate syntax), and
two trace-only mypyvy models with no safety property. Exact paths and reasons
are in the generated manifest. No `true` placeholder properties are emitted.

## Encoding choices to audit

- Mutable functions and relations become scalar nested arrays. Every state
  symbol has an explicit `:next` pair. Rigid symbols have frozen pairs because
  unpaired scalar declarations are inputs in Yardbird.
- Axioms and derived definitions constrain the initial state and both states
  of each transition. Derived relations are not framed. Auxiliary proof
  invariants are not silently assumed. If a mypyvy input has ordinary invariants
  but no safety annotation, all its invariants become checked properties; the
  output says so.
- Cubicle action and unsafe parameters are distinct; initialization binders
  need not be. `forall_other` excludes every action parameter. Case updates
  use first-match priority with an unconditional final branch, as upstream does.
  Enumerations have distinct constructors and exhaustive domain axioms.
- Cubicle process witnesses use an uninterpreted sort with injective integer
  rank. Stored `proc` values are integers and may be outside the rank image:
  some protocols explicitly separate `Home` from selected processes. Array
  indices in the supported grammar are process witnesses. Legacy global-index
  reads are rejected. `number_procs` constrains the witness domain exactly.
- MCMT global declarations are scalars even when written `G[j]`. Updates retain
  declaration order, Lambda's special first-x/second-y cases, disjunctive
  universal guards, and unconstrained uncovered cases. Transition parameters
  are not implicitly distinct; unsafe witnesses are.
- **MCMT compatibility profile:** `nat` and subrange data use Int without
  additional range constraints, matching Lambda. This is not a claim about
  all historical MCMT implementations. `index_arrays` comments are semantic:
  their pointer-range/sentinel axioms are retained. Witnesses use an injective
  Proc-to-Int map rather than quantifying over all integers.
- Unbounded first-order process encodings also admit infinite domains. No
  general finiteness axiom is supplied. Finite counterexamples and shallow
  bounded results must not be presented as full parameterized proofs.
- Ivy's non-global temporary symbols can vary between steps. Undeclared
  initialization values remain unconstrained. Numeric `:sort` hints do not
  impose finite domains. The multisig importer rejects sequencing outside its
  supported subset rather than guessing at it.

See `plans/mypyvy-ivy-translation-semantics.md` and
`plans/cubicle-mcmt-translation-semantics.md` for the primary-source audit.

## Validation and execution

The independent SMT reader type-checks each complete initial, transition, and
property formula before writing. Semantic tests check frame preservation,
derived next-state constraints, quantifier scope, parameter distinctness,
simultaneous assignments, enumeration coverage, real rationals, process values
outside the selected domain, MCMT case semantics, and per-step Ivy temporaries.

```sh
python -m tools.benchmark_translation.smoke --all-parse
python -m tools.benchmark_translation.smoke
```

The first command runs Yardbird at depth zero on every generated file, testing
parsing and setup only. The second checks 12 representative models using both
concrete and abstract strategies at `-d 3` (states 0–2), with a five-second
cooperative limit and an eight-second external limit. Raw JSON results stay in
the ignored `benchmark_results/investigations/offline-import-smoke/` directory.
The checked-in validation summary is beside the generated inputs.
