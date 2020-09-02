; from Tons Of Inductive Problems
; property: (length xs = 0) <=> (xs = [])

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

; the actual property
(assert
	(forall ((l (Tsil AB)))
		(<=>
			(length l 0)
			(= l lin)
		)
	)
)

(check-sat)
(get-model)
