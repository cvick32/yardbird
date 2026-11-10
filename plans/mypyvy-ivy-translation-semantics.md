# Offline mypyvy and Ivy translation semantics

Inspected the pinned source archive `/tmp/yardbird-bulk-mypyvy.tar.gz` and the imported IvyBench sources on 2026-10-31. This is source inspection, not a completed equivalence proof. The originals should remain byte-identical; generated VMT and a source hash/options manifest should be separate files.

## mypyvy: use the upstream front end, emit SMT directly

The pinned version is `cd80557ae11f5958c7c81dbecf3b24f7a3b16c1f`. The minimal front end is `parser`, `syntax`, `utils`, and `typechecker`, with the **bundled modified PLY**, `z3`, and `typing_extensions`. Full `mypyvy.py` imports verification/inference modules; `translator.py` additionally imports networkx, solver_cvc4, semantics, and z3_utils. Avoid those dependency chains if emitting SMT directly. The bundled parser calls nonstandard PLY `forbid_rebuild` and lexer filename support, so vanilla installed PLY is not an equivalent replacement. Source: [parser.py](https://github.com/wilcoxjay/mypyvy/blob/cd80557ae11f5958c7c81dbecf3b24f7a3b16c1f/src/parser.py), [syntax.py](https://github.com/wilcoxjay/mypyvy/blob/cd80557ae11f5958c7c81dbecf3b24f7a3b16c1f/src/syntax.py), [translator.py](https://github.com/wilcoxjay/mypyvy/blob/cd80557ae11f5958c7c81dbecf3b24f7a3b16c1f/src/translator.py).

Parse with `parser.get_parser().parse(input=text, lexer=parser.get_lexer(), filename=path)`, assign `prog.input`, then `typechecker.typecheck_program(prog)`. Initialize `utils.args` with error/reporting settings (`error_filename_basename`, `exit_on_error`, `json`), and reset/check `utils.error_count` per file. Typechecking closes free uppercase variables universally and resolves omitted binder sorts; it is essential, not an optional parser check. Source: [mypyvy.py:562](https://github.com/wilcoxjay/mypyvy/blob/cd80557ae11f5958c7c81dbecf3b24f7a3b16c1f/src/mypyvy.py#L562), [typechecker.py:323](https://github.com/wilcoxjay/mypyvy/blob/cd80557ae11f5958c7c81dbecf3b24f7a3b16c1f/src/typechecker.py#L323), [utils.py:144](https://github.com/wilcoxjay/mypyvy/blob/cd80557ae11f5958c7c81dbecf3b24f7a3b16c1f/src/utils.py#L144).

The semantic contract is:

- Mutable constants, relations, and functions have current/next versions. Immutable symbols retain one interpretation for the whole trace.
- `new(e)` advances the state context of all mutable occurrences in `e`. `f'(g(x))` advances **f only**; its argument `g(x)` stays in the enclosing state. A generic identifier suffix replacement does not preserve this distinction.
- `DefinitionDecl.as_twostate_formula(scope)` supplies the needed action semantics: existential action arguments, the declared body, and frame equalities for all mutable symbols outside `modifies`. Positive-arity frames are universally quantified pointwise equalities.
- Derived relations are excluded from frames. Their `derived_axiom` must hold at **every** state. Ordinary immutable axioms are asserted once; the upstream solver adds derived axioms on each newly introduced state.
- Expand definition macros using `syntax.expand_macros(scope, expr)`, preserving lexical binders. Ordinary helper invariants are not transition assumptions. Use declared safeties as the default safety property, recording any explicit fallback to ordinary invariants.

These follow directly from [syntax.py:1122](https://github.com/wilcoxjay/mypyvy/blob/cd80557ae11f5958c7c81dbecf3b24f7a3b16c1f/src/syntax.py#L1122), [translator.py:85](https://github.com/wilcoxjay/mypyvy/blob/cd80557ae11f5958c7c81dbecf3b24f7a3b16c1f/src/translator.py#L85), and [solver.py:73](https://github.com/wilcoxjay/mypyvy/blob/cd80557ae11f5958c7c81dbecf3b24f7a3b16c1f/src/solver.py#L73).

All 126 imported mypyvy models use the current `new`/prime dialect after comments are stripped; five apparent `old(...)` occurrences are only comments. Four models lack `safety` declarations: `misc/indigo_tournament.pyv` and `misc/chain_replication.pyv` have ordinary invariants; `misc/derived-relations/paxos_autorelaxed.pyv` and `paxos_relaxed.pyv` instead contain explicit satisfiable trace assertions. The latter two need a documented derived property or a recorded unsupported status; emitting `true` as a successful safety benchmark would hide missing semantics. Sources: the four imported files under [mypyvy examples](../examples/quantified-transition-systems/mypyvy/examples/misc/).

## IvyBench existing VMT: reconstruct complete transitions

The 54 imported VMT files are an extended dialect: all have `:action`; 38 have `:axiom`; 42 have `:global`; 19 have `:definition`. Keep annotation meaning when producing ordinary `:init`, `:trans`, and `:invar-property` formulas. Source: [imported corpus](../examples/quantified-transition-systems/ivybench/) at IvyBench commit `d2c9298fdd099001c71a34bc2e118db6f07d8404`.

| Input feature | Required interpretation |
|---|---|
| `(! (__r args) :next r)` | `__r` is current, `r` is next, including positive-arity functions. |
| `:global true` | Time-independent immutable symbol. |
| `:axiom true` | Background assumptions; preserve in initialization/transition constraints rather than discarding annotations. |
| `:definition symbol` | Definitional constraint; current definitions in init and current/next definitions in trans. Never frame derived state. |
| `:action action_name` | One disjunct of trans, plus frame equalities for untouched non-derived state. |
| `:sort` | Export metadata, not a finite-domain axiom; do not bound the sort from its numeric value. |

Examples: [lock_server.vmt](../examples/quantified-transition-systems/ivybench/i4/vmt/lock_server.vmt), [Paxos.vmt](../examples/quantified-transition-systems/ivybench/paxos/vmt/Paxos.vmt), [distributed_lock.vmt](../examples/quantified-transition-systems/ivybench/i4/vmt/distributed_lock.vmt). Paxos has definitions for **both** `__chosen` and `chosen`, etc. Distributed lock `grant` omits `locked` and `ep`, which must be preserved. Cross-check omitted-next-symbol frame inference against the companion PYV modifies list; do not equate arbitrary absent constraints with preservation in a language that supports havoc.

**Additional action temporaries must not become immutable globals.** Fifteen files have declared symbols that are neither paired state nor `:global`: Boolean `__ts*` and `__fml:nondet` witnesses, and in six files the higher-arity relation `__m_pending`. In distributed lock, `__ts0_a` is equated to the current guard in `accept`; persisting one interpretation across all BMC frames would prohibit switching branch outcomes. In [ring.vmt](../examples/quantified-transition-systems/ivybench/ex/vmt/ring.vmt), `__m_pending` has a partially unconstrained tuple, so it cannot simply be expanded as a total deterministic definition.

A uniform first-order encoding is to give each temporary an artificial current/next state pair, leave initialization unconstrained, and **never add frames for temporaries**. The action constrains only its current-step temporary; the next temporary remains free. Existentially binding each nullary temporary per action also works; higher-arity symbols need an array representation or state-pair encoding, not invalid first-order function quantification. Source evidence: [distributed_lock.vmt](../examples/quantified-transition-systems/ivybench/i4/vmt/distributed_lock.vmt), [ring.vmt](../examples/quantified-transition-systems/ivybench/ex/vmt/ring.vmt), [learning_switch.vmt](../examples/quantified-transition-systems/ivybench/mypyv/vmt/learning_switch.vmt).

Quote colon-bearing names and reserved identifiers consistently using a parsed symbol table. Preserve the original property and unbounded sort semantics. These normalizations should be explicit in generated-file comments/manifest.

## Legacy PYV and the four Ivy-only models

All 54 IvyBench PYVs use the old state convention: unadorned transition occurrences mean **post-state**, and `old(e)` means pre-state. Current mypyvy uses the opposite default with `new(e)`. Migration must be AST/context aware, preserve bound variables and immutable symbols, and leave init/property formulas in one-state context. A textual `old` to `new` replacement is wrong. Compare [old lock_server.pyv](../examples/quantified-transition-systems/ivybench/i4/pyv/lock_server.pyv) with its paired VMT above. The existing VMT route avoids this migration entirely while retaining the original Ivy translation.

The four [multisig Ivy models](../examples/quantified-transition-systems/ivybench/multisig/ivy/) have a small explicit subset: uninterpreted types; Boolean relations (including nullary `holding`); two derived relations in the majority variants; quantifiers and Boolean formulas; `after init`; five exported actions; `require`; Boolean point/slice updates; and three invariants. A strict subset exporter is realistic without installing upstream Ivy. Reject anything outside this grammar rather than silently accepting a general Ivy program.

For those four files:

- Infer uppercase variable sorts from relation arguments and universally close free formula variables; existentially bind lowercase action arguments.
- `r(k,v,d,S) := false` updates the entire `S` slice, keeping all other tuples. Build pointwise `ite` equations; preserve untouched relations per action. The observed assignments are to distinct relations within an action, with requirements preceding updates, so no complex sequencing machinery is needed for these exact files.
- `sig_auth` and `member` are never assigned, hence can remain immutable. `expired` is mutable, but has **no initializer**: its initial interpretation is unconstrained. Do not infer false from missing initialization.
- Enforce `chosenAt`/`chosen` definitions at every state, preserve the majority quorum-intersection axiom, and check the conjunction of the three uncommented invariants. The bottom commented proof-certificate suggestions are not properties.

Suggested semantic tests: untouched-function preservation; two-step changes to an auxiliary Boolean; two different per-step `__m_pending` relations; current versus next derived predicates; bulk slice update keeping other tuples; and unconstrained initial `expired`. Parsing/typechecking alone does not establish these properties.
