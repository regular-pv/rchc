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
  (forall ( (x Nat) ) (=> (even x) (odd (s x))) )
)
(assert
  (even zero)
)
(assert
  (forall ( (x Nat) ) (not (and (even x) (odd x))))
)


(check-sat)
(get-model)
