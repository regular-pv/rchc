(set-logic HORN)

(declare-fun eq ( Nat Nat ) Bool)

(assert
  (eq 0 0)
)

(assert
	(forall ((x Nat)) (not (eq 0 (s x))))
)

(assert
	(forall ((x Nat)) (not (eq (s x) 0)))
)

(assert
  (forall ( (x Nat) (y Nat) ) (<=> (eq x y) (eq (s x) (s y))) )
)

(check-sat)
(get-model)
