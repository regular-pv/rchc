(set-logic HORN)

; declare predicates
(declare-fun even ( Nat ) Bool)
(declare-fun odd ( Nat ) Bool)

(assert
  (forall ( (x Nat) ) (=> (even x) (odd (s x))) )
)
(assert
  (forall ( (x Nat) ) (=> (odd x) (even (s x))) )
)
(assert
  (even 0)
)
(assert
  (forall ( (x Nat) ) (not (and (even x) (odd x))))
)


(check-sat)
(get-model)
