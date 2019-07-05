(set-logic HORN)

(declare-datatypes ( (Nat 0) )
  (
    ( (zero) (s (succ Nat)) )
  )
)

; declare predicates
(declare-fun even ( Nat ) Bool)
(declare-fun odd ( Nat ) Bool)

(assert
  (forall ( (x Nat) ) (=> (even x) (even (s (s x)))) )
)
(assert
  (forall ( (x Nat) ) (=> (odd x) (odd (s (s x)))) )
)
(assert
  (even zero)
)

(check-sat)
(get-model)
