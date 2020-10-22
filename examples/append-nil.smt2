; from Tons Of Inductive Problems
; property: append l nil = l

(declare-fun append ( (List AB) (List AB) (List AB) ) Bool) ; over-approx

; append nil l2 -> l2
; append (cons x l1) l2 -> (cons x (append l1 l2))

(assert
	(forall ((l2 (List AB))) (append nil l2 l2))
)
(assert
	(forall ((x AB) (l1 (List AB)) (l2 (List AB)) (l3 (List AB)))
		(=>
			(append l1 l2 l3)
			(append (insert x l1) l2 (insert x l3))
		)
	)
)

; actual property
(assert
	(forall ((k (List AB)) (l (List AB))) (=> (append k nil l) (= k l)))
)

(check-sat)
