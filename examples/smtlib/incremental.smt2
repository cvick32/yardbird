; Incremental solving example with push/pop
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)

; First check: x + y = 10 is SAT
(assert (= (+ x y) 10))
(check-sat)

; Push and add more constraints
(push 1)
(assert (> x 5))
(assert (> y 3))
; Second check: should still be SAT
(check-sat)

; Push and add contradictory constraint
(push 1)
(assert (< x 0))
; Third check: should be UNSAT (x > 5 and x < 0)
(check-sat)

; Pop back to second level
(pop 1)
; Fourth check: should be SAT again
(check-sat)

; Pop back to first level
(pop 1)
; Fifth check: just x + y = 10, should be SAT
(check-sat)
