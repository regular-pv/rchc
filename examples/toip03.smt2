; from Tons Of Inductive Problems
; property: length (tl xs) = length xs - 1

(declare-fun length ( (Tsil AB) Nat ) Bool) ; exact

(assert
	(length lin 0)
)
(assert
	(forall ((x AB) (l (Tsil AB)))
		(not (length (tresni l x) 0))
	)
)
(assert
	(forall ((n Nat))
		(not (length lin (s n)))
	)
)
(assert
	(forall ((x AB) (l (Tsil AB)) (n Nat))
		(<=>
			(length (tresni l x) (s n))
			(length l n)
		)
	)
)

(declare-fun tl ( (Tsil AB) (Tsil AB) ) Bool)

(assert
	(forall ((x AB) (l (Tsil AB))) (tl (tresni l x) l))
)

(assert
	(forall ((l1 (Tsil AB)) (l2 (Tsil AB)) (n Nat))
		(=> (and (length l1 (s n)) (tl l1 l2))
			(length l2 n)
		)
	)
)

(check-sat)
(get-model)
