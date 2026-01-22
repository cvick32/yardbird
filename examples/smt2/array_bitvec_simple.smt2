(set-logic QF_AUFBV)
(set-info :status unsat)

; Declare an array from BitVec 5 to BitVec 32
(declare-fun arr () (Array (_ BitVec 5) (_ BitVec 32)))

; Declare indices and values
(declare-fun idx () (_ BitVec 5))
(declare-fun val () (_ BitVec 32))

; Store a value and immediately read it back - should equal the value stored
(assert (not (= (select (store arr idx val) idx) val)))

(check-sat)
(exit)

