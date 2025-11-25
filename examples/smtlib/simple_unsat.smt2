; Simple UNSAT example
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 10))
(assert (< x 5))
(check-sat)
