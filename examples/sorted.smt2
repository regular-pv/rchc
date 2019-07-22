(set-logic HORN)

(declare-datatypes ( (List 0) )
  (
    ( (nil) (cons (tail List) (value Bool)) )
  )
)

; declare predicates
(declare-fun sorted ( List ) Bool)
(declare-fun all_false ( List ) Bool)

(assert
  (forall ( (l List) ) (=> (sorted l) (sorted (cons l true)) ) )
)
(assert
  (forall ( (l List) ) (=> (all_false l) (sorted (cons l false)) ) )
)
(assert
  (sorted nil)
)
(assert
  (forall ( (l List) ) (not (sorted (cons (cons l true) false))))
)

(assert
  (forall ( (l List) ) (=> (all_false l) (all_false (cons l false)) ) )
)
(assert
  (all_false nil)
)

(check-sat)
(get-model)
