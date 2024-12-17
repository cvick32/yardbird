# to_vmt macro

This crate provides the `to_vmt` proc macro for functions. It parses a function into VMT and runs yardbird to try to get a proof. 

There's still quite a few modeling problems and TODOs to clean up: 

- handle for and while loops
- handle nested loops
  - not sure if this was in any of the given benchmarks
- handle multiple loops
  - deal with program counter 

