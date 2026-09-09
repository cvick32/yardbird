# Distributed protocol benchmarks

These protocols were originally written in Ivy and transpiled to VMT using
Ivy. They are included in Yardbird with reuse permission from the owner of the
Ivy repository, as communicated to the Yardbird maintainer.

Each original also has a `*.encoding.vmt` companion beside it, with array
lambdas replaced by equivalent pointwise constraints. See [ENCODINGS.md](ENCODINGS.md)
for the rules, manual-audit commands, equivalence checks, and comparison runner.
The originals are preserved.

## Abstract strategy

Run a protocol with Yardbird-managed array and quantifier instantiation:

```sh
cargo run --release -- -f examples/distributed_protocols/consensus_forall/consensus_forall.vmt -s abstract -d 5
```

The abstract strategy lowers `forall`, `exists`, and array `lambda` expressions
throughout initial conditions, transitions, properties, background assertions,
and helper definitions. Nested quantifiers, multiple binders, and either Boolean
polarity are supported. Lexical binders are renamed before expanding lets so
substitution and property witnesses cannot capture free variables.

Ground background-axiom terms are registered at each BMC frame in a persistent
source-term collection. This makes their Boolean helpers available to quantifier
instantiation and their array reads/writes available to array refinement, even
when initial or property terms are regenerated.

This is an incomplete instantiation procedure, not a finite-domain encoding.
Each pass has tuple and instance limits, in addition to the normal refinement
limit. Exhaustion reports an inconclusive result. Quantified inputs never fall
back to concrete solver quantifiers, including for interpolation validation;
an abstract SAT model alone is not reported as a real counterexample.

## Regression coverage

```sh
cargo test --release --test distributed_protocol_quantifier_tests
cargo test --lib quantifier_abstraction::tests
```

The original corpus test discovers all 31 original `.vmt` files in this directory,
including the German ghost-state variant, checks depth 0, and inspects the
captured solver transcript for quantifiers and lambdas. A separate transition
test checks depths 0–1 for client/server AE, client/server DB AE, consensus forall,
two-phase commit, and Tomasulo. Both lock servers and two-phase commit have
depth-5 transcript tests; German retains its existing depth-5 regression.
A background-axiom regression checks initial and later-frame instances across
three depths, including that solver transcripts remain quantifier-free.
Database chain replication has a depth-2 transcript regression using its original
background assertions. Each protocol gets 60 seconds in release builds or 300
seconds in unoptimized debug builds.
These bounds are regression coverage, not a claim that every protocol terminates
at arbitrary depths; larger protocols can still time out or exhaust refinement.

Before persistent background-axiom registration, release-build measurements on
2026-09-06 completed `-d 2` for 25 of the 31 files with a 60-second limit per file.
Fast Paxos, Paxos, stoppable Paxos, and
hybrid reliable broadcast timed out; database chain replication and the German
ghost-state variant exhausted refinement at depth 1. A selected `-d 5` run also
completed client/server AE, both lock servers, two-phase commit, and German.
All completed runs reported zero concrete-validation checks.
