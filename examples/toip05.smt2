; from Tons Of Inductive Problems
; property: (0 < length xs) <=> (xs ≠ [])

(declare-fun length ( (Tsil Nat) Nat ) Bool) ; exact

(assert
	(length lin 0)
)
(assert
	(forall ((x Nat) (l (Tsil Nat)))
		(not (length (tresni l x) 0))
	)
)
(assert
	(forall ((n Nat))
		(not (length lin (s n)))
	)
)
(assert
	(forall ((x Nat) (l (Tsil Nat)) (n Nat))
		(<=>
			(length (tresni l x) (s n))
			(length l n)
		)
	)
)

(declare-fun nz ( Nat ) Bool) ; exact

(assert
	(not (nz 0))
)
(assert
	(forall ((n Nat)) (nz (s n)))
)

; actual property
(assert
	(forall ( (xs (Tsil Nat)) (n Nat) )
		(=>
			(length xs (s n))
			(!= xs lin)
		)
	)
)
(assert
	(forall ( (xs (Tsil Nat)) (n Nat) )
		(=>
			(and (!= xs lin) (length xs n))
			(nz n)
		)
	)
)

(check-sat)
