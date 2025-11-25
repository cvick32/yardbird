; Uninterpreted functions example
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun x () Int)
(declare-fun y () Int)

; f and g are functions, and we assert some properties
(assert (= (f x) (g y)))
(assert (= x y))
(assert (not (= (f x) (g x))))
; This should be UNSAT because:
; x = y, so f(x) = g(y) implies f(x) = g(x)
; but we also assert f(x) ≠ g(x)
(check-sat)
