(declare-sort id 0)
(declare-fun a@0 () (Array id id))
(declare-fun x@0 () id)
(declare-fun y@0 () id)
(declare-fun Z@0 () id)
(declare-fun a@1 () (Array id id))
(declare-fun x@1 () id)
(declare-fun y@1 () id)
(declare-fun Z@1 () id)
(declare-fun a@2 () (Array id id))
(declare-fun x@2 () id)
(declare-fun y@2 () id)
(declare-fun Z@2 () id)
(declare-fun a@3 () (Array id id))
(declare-fun x@3 () id)
(declare-fun y@3 () id)
(declare-fun Z@3 () id)
(declare-fun a@4 () (Array id id))
(declare-fun x@4 () id)
(declare-fun y@4 () id)
(declare-fun Z@4 () id)
(declare-fun a@5 () (Array id id))
(declare-fun x@5 () id)
(declare-fun y@5 () id)
(declare-fun Z@5 () id)
(declare-fun a@6 () (Array id id))
(declare-fun x@6 () id)
(declare-fun y@6 () id)
(declare-fun Z@6 () id)
(declare-fun a@7 () (Array id id))
(declare-fun x@7 () id)
(declare-fun y@7 () id)
(declare-fun Z@7 () id)
(declare-fun a@8 () (Array id id))
(declare-fun x@8 () id)
(declare-fun y@8 () id)
(declare-fun Z@8 () id)
(declare-fun a@9 () (Array id id))
(declare-fun x@9 () id)
(declare-fun y@9 () id)
(declare-fun Z@9 () id)
(declare-fun a@10 () (Array id id))
(declare-fun x@10 () id)
(declare-fun y@10 () id)
(declare-fun Z@10 () id)
(assert (= a@0 ((as const (Array id id)) Z@0)))
(assert (and (= a@1 (store a@0 x@0 (select a@0 y@0))) (= Z@1 Z@0)))
(assert (and (= a@2 (store a@1 x@1 (select a@1 y@1))) (= Z@2 Z@1)))
(assert (and (= a@3 (store a@2 x@2 (select a@2 y@2))) (= Z@3 Z@2)))
(assert (and (= a@4 (store a@3 x@3 (select a@3 y@3))) (= Z@4 Z@3)))
(assert (and (= a@5 (store a@4 x@4 (select a@4 y@4))) (= Z@5 Z@4)))
(assert (and (= a@6 (store a@5 x@5 (select a@5 y@5))) (= Z@6 Z@5)))
(assert (and (= a@7 (store a@6 x@6 (select a@6 y@6))) (= Z@7 Z@6)))
(assert (and (= a@8 (store a@7 x@7 (select a@7 y@7))) (= Z@8 Z@7)))
(assert (and (= a@9 (store a@8 x@8 (select a@8 y@8))) (= Z@9 Z@8)))
(assert (and (= a@10 (store a@9 x@9 (select a@9 y@9))) (= Z@10 Z@9)))
(assert (= (select a@10 x@10) Z@10))
(check-sat)