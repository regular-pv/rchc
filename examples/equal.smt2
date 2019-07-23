(set-logic HORN)

(declare-datatypes ( (Nat 0) )
  (
    ( (zero) (s (succ Nat)) )
  )
)

; declare predicates
(declare-fun eq ( Nat Nat ) Bool)

(assert
  (forall ( (x Nat) (y Nat) ) (=> (eq x y) (eq (s x) (s y))) )
)
(assert
  (eq zero zero)
)
(assert
	(forall ( (x Nat) (y Nat) (z Nat) ) (=> (and (eq x y) (eq y z)) (eq x z)))
)
(assert
	(forall ((x Nat)) (not (eq zero (s x))))
)
(assert
	(forall ((x Nat)) (not (eq (s x) zero)))
)
(assert
	(forall ((x Nat) (y Nat)) (=> (not (eq x y)) (not (eq (s x) (s y)))))
)

(check-sat)
(get-model)
