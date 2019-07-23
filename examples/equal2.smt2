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
	(forall ( (x Nat) (y Nat) (z Nat) ) (=> (and (eq x y) (eq y z)) (= x z)))
)

(check-sat)
(get-model)
