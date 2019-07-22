(set-logic HORN)

; the program:
; let insert x = function
;	| nil -> x::nil
;	| y::l -> if x <= y then x::y::l else y::(insert x l)

; the property:
; forall x. forall l. (length (insert x l)) = s (length l)

(declare-datatypes ( (AB 0) )
  (
    ( (a) (b) )
  )
)

(declare-datatypes ( (List 0) )
  (
    ( (nil) (conss (tail List) (value AB)) )
  )
)

; declare predicates
(declare-fun sorted ( List ) Bool)
(declare-fun all_false ( List ) Bool)

(assert
  (forall ( (x AB) ) (eq (length (cons nil x)) 0) )
)

(check-sat)
(get-model)
