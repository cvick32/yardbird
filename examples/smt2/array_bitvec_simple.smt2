(set-logic QF_AUFBV)
(set-info :status sat)

; Declare an array from BitVec 5 to BitVec 32
(declare-fun arr () (Array (_ BitVec 5) (_ BitVec 32)))

; Declare indices and values
(declare-fun idx1 () (_ BitVec 5))
(declare-fun idx2 () (_ BitVec 5))
(declare-fun val1 () (_ BitVec 32))
(declare-fun val2 () (_ BitVec 32))

; Test array operations
(assert (= val1 (select arr idx1)))
(assert (= (select (store arr idx2 val2) idx2) val2))

; Make it satisfiable by constraining one value
(assert (= val1 #x00000001))

(check-sat)
(exit)
