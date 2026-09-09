# Filtered SMTInterpol Predicate Dumps

Generated from real Yardbird auxiliary-synthesis runs at BMC depth 8 with `--synthesis-trigger non-local --synthesis-guard-policy interpolant`.

The catalog removes variable-free predicates, reflexive relations, and duplicates under symmetric/commutative normalization before this dump is produced.

| Benchmark | Raw | Filtered | Removed |
|---|---:|---:|---:|
| `array_init_increm_two_arrs_const` | 44 | 43 | 1 |
| `array_init_increm_two_arrs` | 50 | 42 | 8 |
| `array_copy_inverse` | 106 | 79 | 27 |

Each retained candidate records the sequence interpolant(s) that supplied it, its free framed variables, and the original parsed SMT term.

## array_init_increm_two_arrs_const

Source: `examples/array/array_init_increm_two_arrs_const.vmt`

Filtered candidates: 43

```text
candidate=0 interpolants={0} variables={PredicateVariable { name: "pc", frame: Some(0) }} term=(= (+ pc@0 (- 1)) 0)
candidate=1 interpolants={0} variables={PredicateVariable { name: "N", frame: Some(0) }, PredicateVariable { name: "i", frame: Some(0) }} term=(<= i@0 (+ N@0 (- 2)))
candidate=2 interpolants={0} variables={PredicateVariable { name: "i", frame: Some(0) }} term=(<= i@0 0)
candidate=3 interpolants={0} variables={PredicateVariable { name: "N", frame: Some(0) }} term=(<= 0 (+ N@0 (- 2)))
candidate=4 interpolants={1} variables={PredicateVariable { name: "pc", frame: Some(1) }} term=(= (+ pc@1 (- 1)) 0)
candidate=5 interpolants={1} variables={PredicateVariable { name: "N", frame: Some(1) }, PredicateVariable { name: "i", frame: Some(1) }} term=(<= i@1 (+ N@1 (- 1)))
candidate=6 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }} term=(<= i@1 1)
candidate=7 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }} term=(<= (+ i@1 (- 1)) 0)
candidate=8 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }} term=(< (+ i@1 (- 1)) 0)
candidate=9 interpolants={1} variables={PredicateVariable { name: "b", frame: Some(1) }, PredicateVariable { name: "i", frame: Some(1) }, PredicateVariable { name: "x", frame: Some(1) }} term=(= x@1 (select (store b@1 i@1 x@1) 0))
candidate=10 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }} term=(= 0 i@1)
candidate=11 interpolants={1} variables={PredicateVariable { name: "N", frame: Some(1) }} term=(<= 0 (+ N@1 (- 2)))
candidate=12 interpolants={2} variables={PredicateVariable { name: "pc", frame: Some(2) }} term=(= (+ pc@2 (- 1)) 0)
candidate=13 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }} term=(<= (+ i@2 (- 1)) 1)
candidate=14 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }} term=(< (+ i@2 (- 1)) 1)
candidate=15 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }} term=(<= (+ i@2 (- 2)) 0)
candidate=16 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }} term=(< (+ i@2 (- 2)) 0)
candidate=17 interpolants={2} variables={PredicateVariable { name: "b", frame: Some(2) }} term=(= (select b@2 1) (select b@2 0))
candidate=18 interpolants={2} variables={PredicateVariable { name: "a", frame: Some(2) }, PredicateVariable { name: "b", frame: Some(2) }} term=(= (select a@2 1) (select b@2 0))
candidate=19 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }} term=(<= i@2 2)
candidate=20 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }} term=(<= i@2 1)
candidate=21 interpolants={2} variables={PredicateVariable { name: "N", frame: Some(2) }} term=(<= 0 (+ N@2 (- 2)))
candidate=22 interpolants={3} variables={PredicateVariable { name: "pc", frame: Some(3) }} term=(= (+ pc@3 (- 1)) 0)
candidate=23 interpolants={3} variables={PredicateVariable { name: "N", frame: Some(3) }, PredicateVariable { name: "i", frame: Some(3) }} term=(<= (+ N@3 (- 1)) (+ i@3 1))
candidate=24 interpolants={3} variables={PredicateVariable { name: "N", frame: Some(3) }, PredicateVariable { name: "i", frame: Some(3) }} term=(< (+ N@3 (- 1)) (+ i@3 1))
candidate=25 interpolants={3} variables={PredicateVariable { name: "N", frame: Some(3) }, PredicateVariable { name: "i", frame: Some(3) }} term=(<= N@3 (+ i@3 1))
candidate=26 interpolants={3} variables={PredicateVariable { name: "b", frame: Some(3) }, PredicateVariable { name: "i", frame: Some(3) }} term=(= (select (store b@3 i@3 (+ (select b@3 i@3) 1)) (+ i@3 1)) (select b@3 i@3))
candidate=27 interpolants={3} variables={PredicateVariable { name: "a", frame: Some(3) }, PredicateVariable { name: "b", frame: Some(3) }, PredicateVariable { name: "i", frame: Some(3) }} term=(= (select (store a@3 i@3 (+ (select a@3 i@3) 1)) (+ i@3 1)) (select b@3 i@3))
candidate=28 interpolants={3} variables={PredicateVariable { name: "N", frame: Some(3) }} term=(<= (+ N@3 (- 1)) 1)
candidate=29 interpolants={3} variables={PredicateVariable { name: "N", frame: Some(3) }} term=(< (+ N@3 (- 1)) 1)
candidate=30 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }} term=(= 1 (+ i@3 1))
candidate=31 interpolants={3} variables={PredicateVariable { name: "N", frame: Some(3) }} term=(<= 0 (+ N@3 (- 2)))
candidate=32 interpolants={3} variables={PredicateVariable { name: "N", frame: Some(3) }, PredicateVariable { name: "i", frame: Some(3) }} term=(<= i@3 (+ N@3 (- 2)))
candidate=33 interpolants={4} variables={PredicateVariable { name: "pc", frame: Some(4) }} term=(= (+ pc@4 (- 1)) 0)
candidate=34 interpolants={4} variables={PredicateVariable { name: "N", frame: Some(4) }, PredicateVariable { name: "i", frame: Some(4) }} term=(<= N@4 i@4)
candidate=35 interpolants={4} variables={PredicateVariable { name: "N", frame: Some(4) }} term=(<= (+ N@4 (- 1)) 1)
candidate=36 interpolants={4} variables={PredicateVariable { name: "N", frame: Some(4) }} term=(< (+ N@4 (- 1)) 1)
candidate=37 interpolants={4} variables={PredicateVariable { name: "i", frame: Some(4) }} term=(= 1 i@4)
candidate=38 interpolants={4} variables={PredicateVariable { name: "a", frame: Some(4) }, PredicateVariable { name: "b", frame: Some(4) }, PredicateVariable { name: "i", frame: Some(4) }} term=(<= (select b@4 i@4) (select a@4 i@4))
candidate=39 interpolants={4} variables={PredicateVariable { name: "N", frame: Some(4) }, PredicateVariable { name: "i", frame: Some(4) }} term=(<= N@4 (+ i@4 (- 1)))
candidate=40 interpolants={4} variables={PredicateVariable { name: "N", frame: Some(4) }, PredicateVariable { name: "i", frame: Some(4) }} term=(<= i@4 (+ N@4 (- 2)))
candidate=41 interpolants={4} variables={PredicateVariable { name: "N", frame: Some(4) }, PredicateVariable { name: "i", frame: Some(4) }} term=(<= i@4 (+ N@4 (- 1)))
candidate=42 interpolants={4} variables={PredicateVariable { name: "N", frame: Some(4) }} term=(<= 0 (+ N@4 (- 2)))
```

## array_init_increm_two_arrs

Source: `examples/array/array_init_increm_two_arrs.vmt`

Filtered candidates: 42

```text
candidate=0 interpolants={0} variables={PredicateVariable { name: "pc", frame: Some(0) }} term=(= (+ pc@0 (- 1)) 0)
candidate=1 interpolants={0} variables={PredicateVariable { name: "i", frame: Some(0) }} term=(<= i@0 0)
candidate=2 interpolants={0} variables={PredicateVariable { name: "i", frame: Some(0) }} term=(<= 0 i@0)
candidate=3 interpolants={1} variables={PredicateVariable { name: "pc", frame: Some(1) }} term=(= (+ pc@1 (- 1)) 0)
candidate=4 interpolants={1} variables={PredicateVariable { name: "N", frame: Some(1) }} term=(<= N@1 0)
candidate=5 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }} term=(<= i@1 1)
candidate=6 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }} term=(<= 0 (+ i@1 (- 1)))
candidate=7 interpolants={1} variables={PredicateVariable { name: "a", frame: Some(1) }, PredicateVariable { name: "b", frame: Some(1) }, PredicateVariable { name: "i", frame: Some(1) }, PredicateVariable { name: "x", frame: Some(1) }} term=(= (select (store b@1 i@1 x@1) 0) (select (store a@1 i@1 x@1) 0))
candidate=8 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }} term=(= 0 i@1)
candidate=9 interpolants={1} variables={PredicateVariable { name: "a", frame: Some(1) }, PredicateVariable { name: "i", frame: Some(1) }, PredicateVariable { name: "x", frame: Some(1) }} term=(= x@1 (select (store a@1 i@1 x@1) 0))
candidate=10 interpolants={2} variables={PredicateVariable { name: "N", frame: Some(2) }} term=(<= N@2 0)
candidate=11 interpolants={2} variables={PredicateVariable { name: "N", frame: Some(2) }} term=(<= N@2 1)
candidate=12 interpolants={2} variables={PredicateVariable { name: "pc", frame: Some(2) }} term=(= (+ pc@2 (- 1)) 0)
candidate=13 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }} term=(<= 0 (+ i@2 (- 2)))
candidate=14 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }} term=(<= (+ i@2 (- 1)) 1)
candidate=15 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }} term=(< (+ i@2 (- 1)) 1)
candidate=16 interpolants={2} variables={PredicateVariable { name: "a", frame: Some(2) }, PredicateVariable { name: "b", frame: Some(2) }} term=(= (select b@2 0) (select a@2 0))
candidate=17 interpolants={2} variables={PredicateVariable { name: "a", frame: Some(2) }, PredicateVariable { name: "b", frame: Some(2) }} term=(= (select b@2 1) (select a@2 0))
candidate=18 interpolants={2} variables={PredicateVariable { name: "a", frame: Some(2) }} term=(= (select a@2 1) (select a@2 0))
candidate=19 interpolants={3} variables={PredicateVariable { name: "N", frame: Some(3) }} term=(<= N@3 0)
candidate=20 interpolants={3} variables={PredicateVariable { name: "N", frame: Some(3) }} term=(<= N@3 1)
candidate=21 interpolants={3} variables={PredicateVariable { name: "pc", frame: Some(3) }} term=(= (+ pc@3 (- 1)) 0)
candidate=22 interpolants={3} variables={PredicateVariable { name: "N", frame: Some(3) }} term=(<= 0 (+ N@3 (- 3)))
candidate=23 interpolants={3} variables={PredicateVariable { name: "N", frame: Some(3) }} term=(<= (+ N@3 (- 1)) 1)
candidate=24 interpolants={3} variables={PredicateVariable { name: "N", frame: Some(3) }} term=(< (+ N@3 (- 1)) 1)
candidate=25 interpolants={3} variables={PredicateVariable { name: "pc", frame: Some(3) }} term=(= (+ pc@3 (- 2)) 0)
candidate=26 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }} term=(<= i@3 0)
candidate=27 interpolants={3} variables={PredicateVariable { name: "a", frame: Some(3) }, PredicateVariable { name: "b", frame: Some(3) }, PredicateVariable { name: "i", frame: Some(3) }} term=(= (+ (select b@3 i@3) 1) (+ (select a@3 i@3) 1))
candidate=28 interpolants={3} variables={PredicateVariable { name: "a", frame: Some(3) }, PredicateVariable { name: "b", frame: Some(3) }, PredicateVariable { name: "i", frame: Some(3) }} term=(= (select (store b@3 i@3 (+ (select b@3 i@3) 1)) (+ i@3 1)) (select a@3 i@3))
candidate=29 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }} term=(= 1 (+ i@3 1))
candidate=30 interpolants={3} variables={PredicateVariable { name: "a", frame: Some(3) }, PredicateVariable { name: "b", frame: Some(3) }, PredicateVariable { name: "i", frame: Some(3) }} term=(= (+ (select b@3 i@3) (* (- 1) (select a@3 i@3))) 0)
candidate=31 interpolants={3} variables={PredicateVariable { name: "a", frame: Some(3) }, PredicateVariable { name: "b", frame: Some(3) }, PredicateVariable { name: "i", frame: Some(3) }} term=(= (select b@3 i@3) (select a@3 i@3))
candidate=32 interpolants={3} variables={PredicateVariable { name: "a", frame: Some(3) }, PredicateVariable { name: "i", frame: Some(3) }} term=(= (select (store a@3 i@3 (+ (select a@3 i@3) 1)) (+ i@3 1)) (select a@3 i@3))
candidate=33 interpolants={4} variables={PredicateVariable { name: "N", frame: Some(4) }} term=(<= N@4 0)
candidate=34 interpolants={4} variables={PredicateVariable { name: "N", frame: Some(4) }} term=(<= N@4 1)
candidate=35 interpolants={4} variables={PredicateVariable { name: "pc", frame: Some(4) }} term=(= (+ pc@4 (- 1)) 0)
candidate=36 interpolants={4} variables={PredicateVariable { name: "N", frame: Some(4) }, PredicateVariable { name: "i", frame: Some(4) }} term=(<= i@4 (+ N@4 (- 3)))
candidate=37 interpolants={4} variables={PredicateVariable { name: "N", frame: Some(4) }} term=(<= (+ N@4 (- 1)) 1)
candidate=38 interpolants={4} variables={PredicateVariable { name: "N", frame: Some(4) }} term=(< (+ N@4 (- 1)) 1)
candidate=39 interpolants={4} variables={PredicateVariable { name: "i", frame: Some(4) }} term=(<= i@4 1)
candidate=40 interpolants={4} variables={PredicateVariable { name: "i", frame: Some(4) }} term=(= 1 i@4)
candidate=41 interpolants={4} variables={PredicateVariable { name: "a", frame: Some(4) }, PredicateVariable { name: "b", frame: Some(4) }, PredicateVariable { name: "i", frame: Some(4) }} term=(<= (select b@4 i@4) (select a@4 i@4))
```

## array_copy_inverse

Source: `examples/array/array_copy_inverse.vmt`

Filtered candidates: 79

```text
candidate=0 interpolants={0} variables={PredicateVariable { name: "i", frame: Some(0) }} term=(<= i@0 0)
candidate=1 interpolants={0} variables={PredicateVariable { name: "i", frame: Some(0) }} term=(<= 0 i@0)
candidate=2 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }} term=(<= (+ i@1 (- 1)) 0)
candidate=3 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }} term=(< (+ i@1 (- 1)) 0)
candidate=4 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }, PredicateVariable { name: "n", frame: Some(1) }} term=(<= (+ (* (- 1) n@1) (* (- 1) i@1) 1) (+ (* (- 1) i@1) (* (- 1) n@1) 1))
candidate=5 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }, PredicateVariable { name: "n", frame: Some(1) }} term=(< (+ (* (- 1) n@1) (* (- 1) i@1) 1) (+ (* (- 1) i@1) (* (- 1) n@1) 1))
candidate=6 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }, PredicateVariable { name: "n", frame: Some(1) }} term=(<= (* (- 1) n@1) (+ (* (- 1) n@1) (* (- 1) i@1) 1))
candidate=7 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }, PredicateVariable { name: "n", frame: Some(1) }} term=(< (* (- 1) n@1) (+ (* (- 1) n@1) (* (- 1) i@1) 1))
candidate=8 interpolants={1} variables={PredicateVariable { name: "a", frame: Some(1) }, PredicateVariable { name: "b", frame: Some(1) }, PredicateVariable { name: "n", frame: Some(1) }} term=(= (select a@1 (+ n@1 (- 1))) (select b@1 0))
candidate=9 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }, PredicateVariable { name: "n", frame: Some(1) }} term=(<= (* 2 n@1) (+ (* 2 n@1) i@1 (- 1)))
candidate=10 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }, PredicateVariable { name: "n", frame: Some(1) }} term=(<= (+ i@1 n@1) (+ n@1 1))
candidate=11 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }, PredicateVariable { name: "n", frame: Some(1) }} term=(<= n@1 (+ n@1 i@1 (- 1)))
candidate=12 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }} term=(<= 0 (+ i@1 (- 1)))
candidate=13 interpolants={1} variables={PredicateVariable { name: "i", frame: Some(1) }} term=(= i@1 0)
candidate=14 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(<= (* (- 1) n@2) (+ (* (- 1) n@2) (* (- 1) i@2) 2))
candidate=15 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(< (* (- 1) n@2) (+ (* (- 1) n@2) (* (- 1) i@2) 2))
candidate=16 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(<= n@2 (+ i@2 1))
candidate=17 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(<= i@2 (+ n@2 (- 3)))
candidate=18 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(= (+ n@2 (- 2)) i@2)
candidate=19 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(<= (* (- 1) n@2) (+ (* (- 1) n@2) (* (- 1) i@2) 1))
candidate=20 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(< (* (- 1) n@2) (+ (* (- 1) n@2) (* (- 1) i@2) 1))
candidate=21 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(= (+ n@2 (- 1)) i@2)
candidate=22 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }} term=(= i@2 1)
candidate=23 interpolants={2} variables={PredicateVariable { name: "a", frame: Some(2) }, PredicateVariable { name: "b", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(= (select a@2 (+ n@2 (- 2))) (select b@2 1))
candidate=24 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(<= (+ (* (- 1) i@2) (- 1)) (+ (* (- 1) n@2) (* (- 1) i@2) 2))
candidate=25 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(< (+ (* (- 1) i@2) (- 1)) (+ (* (- 1) n@2) (* (- 1) i@2) 2))
candidate=26 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(<= (+ (* (- 1) i@2) (- 1)) (+ (* (- 1) n@2) (* (- 1) i@2) 1))
candidate=27 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(< (+ (* (- 1) i@2) (- 1)) (+ (* (- 1) n@2) (* (- 1) i@2) 1))
candidate=28 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(<= (+ (* (- 1) n@2) 1) (+ (* (- 1) n@2) (* (- 1) i@2) 2))
candidate=29 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(< (+ (* (- 1) n@2) 1) (+ (* (- 1) n@2) (* (- 1) i@2) 2))
candidate=30 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(<= (+ (* (- 1) n@2) 1) (+ (* (- 1) n@2) (* (- 1) i@2) 1))
candidate=31 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(< (+ (* (- 1) n@2) 1) (+ (* (- 1) n@2) (* (- 1) i@2) 1))
candidate=32 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(<= (+ (* (- 1) n@2) 2) (+ (* (- 1) n@2) (* (- 1) i@2) 2))
candidate=33 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(< (+ (* (- 1) n@2) 2) (+ (* (- 1) n@2) (* (- 1) i@2) 2))
candidate=34 interpolants={2} variables={PredicateVariable { name: "a", frame: Some(2) }, PredicateVariable { name: "b", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(= (select a@2 (+ n@2 (- 1))) (select b@2 0))
candidate=35 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }} term=(= i@2 0)
candidate=36 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(<= (* (- 1) i@2) (+ (* (- 1) n@2) (* (- 1) i@2) 2))
candidate=37 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(< (* (- 1) i@2) (+ (* (- 1) n@2) (* (- 1) i@2) 2))
candidate=38 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(<= (* (- 1) i@2) (+ (* (- 1) n@2) (* (- 1) i@2) 1))
candidate=39 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(< (* (- 1) i@2) (+ (* (- 1) n@2) (* (- 1) i@2) 1))
candidate=40 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(<= (+ (* (- 1) n@2) 2) (+ (* (- 1) n@2) (* (- 1) i@2) 1))
candidate=41 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }, PredicateVariable { name: "n", frame: Some(2) }} term=(< (+ (* (- 1) n@2) 2) (+ (* (- 1) n@2) (* (- 1) i@2) 1))
candidate=42 interpolants={2} variables={PredicateVariable { name: "i", frame: Some(2) }} term=(<= 0 (+ i@2 (- 2)))
candidate=43 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(<= (+ (* (- 1) n@3) i@3 (- 1)) (+ (* (- 1) n@3) 2))
candidate=44 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(< (+ (* (- 1) n@3) i@3 (- 1)) (+ (* (- 1) n@3) 2))
candidate=45 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(<= n@3 i@3)
candidate=46 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(<= i@3 (+ n@3 (- 2)))
candidate=47 interpolants={3} variables={PredicateVariable { name: "a", frame: Some(3) }, PredicateVariable { name: "b", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(= (select a@3 1) (select b@3 (+ n@3 (- 2))))
candidate=48 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(= (+ n@3 (- 1)) i@3)
candidate=49 interpolants={3} variables={PredicateVariable { name: "a", frame: Some(3) }, PredicateVariable { name: "b", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(= (select a@3 0) (select b@3 (+ n@3 (- 2))))
candidate=50 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(= i@3 (+ n@3 (- 2)))
candidate=51 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(<= (+ (* (- 1) n@3) i@3 (- 1)) (+ (* (- 1) n@3) 1))
candidate=52 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(< (+ (* (- 1) n@3) i@3 (- 1)) (+ (* (- 1) n@3) 1))
candidate=53 interpolants={3} variables={PredicateVariable { name: "a", frame: Some(3) }, PredicateVariable { name: "b", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(= (select a@3 1) (select b@3 (+ n@3 (- 1))))
candidate=54 interpolants={3} variables={PredicateVariable { name: "a", frame: Some(3) }, PredicateVariable { name: "b", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(= (select a@3 0) (select b@3 (+ n@3 (- 1))))
candidate=55 interpolants={3} variables={PredicateVariable { name: "a", frame: Some(3) }, PredicateVariable { name: "b", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(= (select a@3 (+ n@3 (- 2))) (select b@3 1))
candidate=56 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }} term=(= i@3 1)
candidate=57 interpolants={3} variables={PredicateVariable { name: "n", frame: Some(3) }} term=(<= (+ n@3 (- 2)) 0)
candidate=58 interpolants={3} variables={PredicateVariable { name: "n", frame: Some(3) }} term=(< (+ n@3 (- 2)) 0)
candidate=59 interpolants={3} variables={PredicateVariable { name: "n", frame: Some(3) }} term=(<= (- 1) (+ (* (- 1) n@3) 2))
candidate=60 interpolants={3} variables={PredicateVariable { name: "n", frame: Some(3) }} term=(< (- 1) (+ (* (- 1) n@3) 2))
candidate=61 interpolants={3} variables={PredicateVariable { name: "n", frame: Some(3) }} term=(<= (- 1) (+ (* (- 1) n@3) 1))
candidate=62 interpolants={3} variables={PredicateVariable { name: "n", frame: Some(3) }} term=(< (- 1) (+ (* (- 1) n@3) 1))
candidate=63 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(<= (+ (* (- 1) n@3) i@3) (+ (* (- 1) n@3) 2))
candidate=64 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(< (+ (* (- 1) n@3) i@3) (+ (* (- 1) n@3) 2))
candidate=65 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(<= (+ (* (- 1) n@3) i@3) (+ (* (- 1) n@3) 1))
candidate=66 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(< (+ (* (- 1) n@3) i@3) (+ (* (- 1) n@3) 1))
candidate=67 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(<= (+ (* (- 1) n@3) i@3 1) (+ (* (- 1) n@3) 2))
candidate=68 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(< (+ (* (- 1) n@3) i@3 1) (+ (* (- 1) n@3) 2))
candidate=69 interpolants={3} variables={PredicateVariable { name: "a", frame: Some(3) }, PredicateVariable { name: "b", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(= (select a@3 (+ n@3 (- 1))) (select b@3 0))
candidate=70 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }} term=(= i@3 0)
candidate=71 interpolants={3} variables={PredicateVariable { name: "n", frame: Some(3) }} term=(<= (+ n@3 (- 1)) 0)
candidate=72 interpolants={3} variables={PredicateVariable { name: "n", frame: Some(3) }} term=(< (+ n@3 (- 1)) 0)
candidate=73 interpolants={3} variables={PredicateVariable { name: "n", frame: Some(3) }} term=(<= 0 (+ (* (- 1) n@3) 2))
candidate=74 interpolants={3} variables={PredicateVariable { name: "n", frame: Some(3) }} term=(< 0 (+ (* (- 1) n@3) 2))
candidate=75 interpolants={3} variables={PredicateVariable { name: "n", frame: Some(3) }} term=(<= 0 (+ (* (- 1) n@3) 1))
candidate=76 interpolants={3} variables={PredicateVariable { name: "n", frame: Some(3) }} term=(< 0 (+ (* (- 1) n@3) 1))
candidate=77 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(<= (+ (* (- 1) n@3) i@3 1) (+ (* (- 1) n@3) 1))
candidate=78 interpolants={3} variables={PredicateVariable { name: "i", frame: Some(3) }, PredicateVariable { name: "n", frame: Some(3) }} term=(< (+ (* (- 1) n@3) i@3 1) (+ (* (- 1) n@3) 1))
```

