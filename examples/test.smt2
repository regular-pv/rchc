(set-logic HORN)

(declare-datatypes ( (Nat 0) )
  (
    ( (zero) (s (succ Nat)) )
  )
)

; declare predicate
(declare-fun f1 ( Nat ) Bool)

(assert
  (forall ( (x Bool) (y Bool) ) (=> x y) )
)

(check-sat) ; bouh
(get-model)
