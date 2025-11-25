; Simple SAT example
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ x y) 10))
(assert (> x 5))
(assert (> y 3))
(check-sat)
