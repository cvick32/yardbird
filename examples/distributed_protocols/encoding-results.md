# Lambda-free encoding results — 2026-09-08

See [ENCODINGS.md](ENCODINGS.md) for the equivalence rules and reproduction commands.

Both strategies use the same 31 companion files and binary. `-d 5` checks depths 0–4, with a 60s process limit and 3 workers. Strategies run separately.

These are exploratory local timings: the concrete batch overlapped an initial-state regression check, and the abstract batch briefly overlapped equivalence checks. Use the supplied runner without other solver workloads for controlled timing measurements.

Completed means every requested depth was UNSAT. Unknown, incomplete, timeout, exhaustion, and counterexample are separate outcomes.

| Protocol | Concrete | Seconds | Abstract | Seconds | Abstract instances |
|---|---|---:|---|---:|---:|
| chord_ring_maintenance | timeout | 60.007 | timeout | 60.012 | — |
| client_server_ae | completed | 0.085 | completed | 15.392 | 3519 |
| client_server_db_ae | completed | 0.079 | completed | 1.762 | 1122 |
| consensus_epr | completed | 0.302 | completed | 6.174 | 2078 |
| consensus_forall | completed | 0.242 | completed | 57.205 | 6092 |
| consensus_wo_decide | completed | 0.198 | completed | 13.202 | 3239 |
| database_chain_replication | completed | 0.728 | timeout | 60.012 | — |
| decentralized_lock | completed | 0.034 | completed | 8.918 | 1896 |
| distributed_lock | completed | 0.032 | timeout | 60.011 | — |
| fast_paxos | completed | 42.257 | timeout | 60.008 | — |
| flash-coherence | completed | 0.136 | completed | 6.389 | 594 |
| flexible_paxos | completed | 0.239 | timeout | 60.012 | — |
| german | completed | 0.032 | completed | 0.578 | 46 |
| german_with_ghost_state | counterexample | 0.019 | exhausted | 0.402 | — |
| hybrid_reliable_broadcast | timeout | 60.007 | timeout | 60.01 | — |
| learning_switch_quad | completed | 0.079 | timeout | 60.014 | — |
| learning_switch_ternary | completed | 0.089 | timeout | 60.013 | — |
| lock_server_async | completed | 0.036 | completed | 3.557 | 856 |
| lock_server_sync | completed | 0.031 | completed | 2.876 | 662 |
| multi_paxos | completed | 0.145 | timeout | 60.011 | — |
| paxos | completed | 0.364 | timeout | 60.012 | — |
| ring_leader_election | completed | 0.064 | timeout | 60.012 | — |
| sharded_key_value_store | completed | 0.085 | timeout | 60.013 | — |
| sharded_kv_no_lost_keys | timeout | 60.006 | timeout | 60.013 | — |
| stoppable_paxos | completed | 9.616 | timeout | 60.011 | — |
| ticket_lock | completed | 0.045 | completed | 1.762 | 684 |
| tomasulo | completed | 1.029 | exhausted | 10.859 | — |
| toy_consensus_epr | completed | 0.041 | completed | 6.72 | 2417 |
| toy_consensus_forall | completed | 0.051 | completed | 6.519 | 2417 |
| two_phase_commit | completed | 0.04 | completed | 1.291 | 514 |
| vertical_paxos | completed | 0.048 | timeout | 60.013 | — |

| Outcome | Concrete | Abstract |
|---|---:|---:|
| completed | 27 | 14 |
| unknown | 0 | 0 |
| timeout | 3 | 15 |
| exhausted | 0 | 2 |
| counterexample | 1 | 0 |
| incomplete | 0 | 0 |
| error | 0 | 0 |

The encodings preserve semantics and remove lambda expressions. The strategies still differ in both array reasoning and quantifier instantiation; this is not an isolated quantifier-instantiation experiment.

For comparison, the original inputs at the same requested depth and 60-second limit completed 21 concrete and 19 abstract runs. Original concrete results included nine array-theory unknowns; the encoded inputs have none. Original abstract results included 11 timeouts and one exhaustion; the encoded inputs have 15 timeouts and two exhaustions.

Raw outputs and JSON results: `.scratch/distributed-quantifiers/encoding-depth5-60s/`. The original measurements remain under `.scratch/distributed-quantifiers/rerun-registration/depth5-60s/`. These bounded results do not establish unbounded safety.
