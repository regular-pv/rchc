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

(check-sat)
(get-model)
