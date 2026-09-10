# Lambda-free protocol companions

Each original `name.vmt` has a companion `name.encoding.vmt` in the same
directory. The originals are unchanged. The companions describe the same
transition systems and properties, using first-order formulas in place of
lambda-valued arrays. They do not change domains, add protocol assumptions,
introduce free symbols or auxiliary state, or alter solver options.

The header names the original and records its SHA-256. Only commands containing
lambdas are reformatted and rewritten. Other commands are copied verbatim.
There are 31 companions: 27 have rewritten commands; flash coherence, German,
German with ghost state, and ticket lock only gain the explanatory header.

## Encoding rules

Array extensionality gives the equivalence

```smt2
(= A (lambda ((i I)) body))
```

```smt2
(forall ((i I)) (= (select A i) body))
```

The generated bound index is fresh and has the original array's index sort.
For nested arrays the rule is repeated only as far as needed to remove the
lambda. Either side of an equality may contain the lambda. Surrounding
negation, implication, quantifiers, and action guards stay in place; in
particular, a negated array equality becomes `not (forall ...)`, never
`forall (not ...)`.

For a lambda inside a stored row, the generator exposes the entries using
read-over-write and read-over-conditional identities:

```smt2
(select (store A k row) i) = (ite (= i k) row (select A i))
(select (ite c A B) i)    = (ite c (select A i) (select B i))
(select (lambda ((i I)) body) x) = body[i := x]
```

For example, Sharded KV's singleton-row assignment is equivalent to:

```smt2
(forall ((N node) (K key) (V value))
  (= (select (select (select new_table N) K) V)
     (ite (= N n)
          (ite (= K k)
               (= V v)
               (select (select (select table n) K) V))
          (select (select (select table N) K) V))))
```

Here `n`, `k`, and `v` abbreviate the original action inputs. The generated
file uses their original names. Constant lambdas also become pointwise
equalities, rather than introducing constant-array constructors. This avoids
depending on Z3's support for either lambda or constant-array extensions in
a selected solver configuration.

Let bindings in affected commands are expanded with simultaneous binding
semantics and capture-avoiding substitution. The generator does not approximate
arbitrary lambdas with a finite number of writes. Unsupported lambda contexts
raise an error instead of silently weakening a formula.

## Manual audit and regeneration

```sh
diff -u examples/distributed_protocols/paxos/paxos.vmt \
        examples/distributed_protocols/paxos/paxos.encoding.vmt

python3 scripts/encode_distributed_protocols.py --check
python3 -m unittest discover -s tests -p test_protocol_encodings.py

# Write each local equivalence obligation and require Z3 to prove it UNSAT.
# UNKNOWN, timeout, or any other result fails verification.
python3 scripts/encode_distributed_protocols.py --check --verify \
  --audit-dir .scratch/protocol-encoding-audit
```

Omit `--check` to regenerate the companions. The verification command uses
the same embedded Z3 as `target/release/yardbird`, with `ALL` for the audit
queries. It does not change the logic used when benchmarking the VMT files.

On 2026-09-08, all **314 local extensionality obligations** were proved
UNSAT by embedded Z3 4.16.0. Additional checks of complete changed commands
proved 38 of 40 equivalent; Z3 returned UNKNOWN on the complete Fast Paxos
and Hybrid Reliable Broadcast transition comparisons. Every constituent
extensionality rewrite in those two commands passed the local check. The
substitution regressions separately cover lexical capture, simultaneous lets,
shadowing, and negation polarity.

Audit artifacts from this run are under
`.scratch/distributed-quantifiers/encoding-audit/`: `obligations/verification.json`
records local proofs and `commands/verification.json` records complete-command
checks. These are distinct from protocol safety results.

## Comparing strategies

The [2026-09-08 results](encoding-results.md) record 27 concrete completions
and 14 abstract completions at depth 5, with no solver-unknown outcomes.
Timeouts, exhausted refinement, and the original ghost-state counterexample
remain separate from completed bounded checks.

```sh
python3 scripts/compare_protocol_encodings.py \
  --depth 5 --timeout 60 --jobs 3 \
  --output .scratch/protocol-encoding-comparison
```

Both strategies receive identical companion files. The runner only counts a
bounded completion when the process succeeds, reports no counterexample, and
records every requested UNSAT depth. Unknown, timeout, refinement exhaustion,
partial/incomplete output, errors, and counterexamples are separate outcomes.
The output directory must be new so prior results cannot be overwritten.

These files remove the lambda encoding difference; the current strategies
still differ in **both native versus abstract array reasoning and quantifier
instantiation**. An experiment isolating only quantifier instantiation needs
both strategies to share the same array reasoning. Pointwise definitions can
also add substantial instantiation work: equivalent encodings are not expected
to have identical performance, and some companions time out even at depth zero.

The original snapshot inventory remains separate. Every companion is parsed
by `lambda_free_companions_parse_and_match_the_original_inventory`, and the
database companion has a depth-5 check that the abstract solver transcript
contains only ground assertions. Original initial-state regressions continue
to test the original files.
