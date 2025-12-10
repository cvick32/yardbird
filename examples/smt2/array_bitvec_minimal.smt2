(set-logic QF_AUFBV)
(set-info :status sat)

; Declare an array from BitVec 8 to BitVec 16
(declare-fun arr () (Array Int (_ BitVec 32)))

; Declare another array with Int indices
(declare-fun arr2 () (Array Int (_ BitVec 32)))

(assert (= arr arr2))

(check-sat)
(exit)
