# Offline import validation — 2026-10-31

Yardbird revision: `925247c99fb18b1fbdf8ac642a50f73cacdaeb0a`, release binary,
Z3 backend, default BMC cost and theory selection. Python validation used
Z3 4.15.4. No Yardbird engine code was changed.

## Corpus checks

- All **725** original candidate/support files retain their recorded SHA-256.
- **455/455** generated models pass independent SMT-LIB syntax/type checking.
- **455/455** pass Yardbird's concrete parser/setup smoke at `-d 0`; this checks
  input compatibility, not safety or transition execution.
- Byte-for-byte regeneration passes with `python -m tools.benchmark_translation --check`.
- **15 semantic regression tests pass**, including frames, derived next-state
  relations, quantified updates, enum coverage, real rationals, process-domain
  separation, MCMT cases/guards, and fresh Ivy temporaries across two steps.

A separate initial-state satisfiability scan, with 300ms per model, returned
**425 sat, 29 unknown, 1 unsat**. The unsat input is
`cubicle/examples/distrib_channels.cub`: the original initializer requires
`Channel_v[z,z1] = 1.0` and `Channel_v[z,z1] = 0.0`. It was preserved and flagged,
not repaired. Unknown is inconclusive, not evidence of an empty state space.

## Bounded sample

Each run used `-d 3` (checking states 0, 1, 2), a five-second cooperative wall
limit and an eight-second external limit, with at most two processes running.
All 12 concrete runs completed through state 2. Five abstract runs completed;
seven timed out. There were no parse failures, counterexamples, or full proofs
in this sample. Completed BMC means only that no counterexample was found in
the checked states.

Paths below omit the `generated-vmt/` prefix.

| Model | Concrete | Abstract |
| --- | --- | --- |
| `mypyvy/examples/lockserv.pyv.vmt` | 0–2 completed | 0–2 completed |
| `mypyvy/examples/client_server_ae.pyv.vmt` | 0–2 completed | Timeout after state 1 |
| `mypyvy/examples/message_passing_litmus.pyv.vmt` | 0–2 completed | 0–2 completed |
| `mypyvy/examples/peterson.pyv.vmt` | 0–2 completed | Timeout after state 1 |
| `cubicle/examples/bakery.cub.vmt` | 0–2 completed | 0–2 completed |
| `cubicle/examples/german.ctc.cub.vmt` | 0–2 completed | Timeout after state 0 |
| `cubicle/examples/peterson_two_proc.cub.vmt` | 0–2 completed | 0–2 completed |
| `lambda/benchmarks/protocols/bakery.in.vmt` | 0–2 completed | 0–2 completed |
| `lambda/benchmarks/protocols/chandra_buggy.in.vmt` | 0–2 completed | Timeout after state 0 |
| `ivybench/i4/vmt/lock_server.vmt.vmt` | 0–2 completed | Timeout after state 1 |
| `ivybench/i4/vmt/distributed_lock.vmt.vmt` | 0–2 completed | Timeout after state 1 |
| `ivybench/multisig/ivy/multisig-all_simple.ivy.vmt` | 0–2 completed | Timeout after state 0 |

Three additional concrete probes used `-d 10`: `lockserv_unsafe.pyv.vmt`
completed states 0–9 without a counterexample; `consensus_unsafe.pyv.vmt` and
`bakery_lamport_bogus.cub.vmt` hit the eight-second external timeout. Source
filenames are not treated as verified expected outcomes.

Reproduce the main sample and initialization scan using:

```sh
python -m tools.benchmark_translation.smoke --all-parse
python -m tools.benchmark_translation.smoke
python -m tools.benchmark_translation.smoke --initial-states
python -m unittest discover -s tests -p test_benchmark_translation.py
```

Raw run records are local in the ignored
`benchmark_results/investigations/offline-import-smoke/` directory. Timing and
timeout outcomes may vary by hardware and load.

## Separate pre-existing test failure

The existing `test_protocol_encodings.py` suite passed 9 tests and failed its
companion-inventory test: the tracked
`examples/distributed_protocols/german/german_with_ghost_state.vmt` has no
`.encoding.vmt` companion. Neither that source, that test, nor the old encoder
was modified by this work. The failure is separate from these generated files.
