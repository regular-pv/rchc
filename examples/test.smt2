(set-logic HORN)

(declare-datatypes ( (Nat 0) )
  (
    ( (zero) (s (succ Nat)) )
  )
)

; declare predicate
(declare-fun f1 ( Nat ) Bool)

(assert
  (forall ( (x Nat) (y Bool) ) (=> (f1 x) y) )
)

(assert
  (not (exists ((x Bool)) x))
)

(check-sat) ; bouh
(get-model)
