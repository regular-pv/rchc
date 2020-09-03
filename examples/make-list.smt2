; length(make_list(n)) = n
;
; NOTE: we use the `Tsil` type instead of `List` so that the
;       standard convolution can be used.
(set-logic HORN)

; make_list function
(declare-fun make_list ( Nat (Tsil Nat) ) Bool)
(assert (make_list 0 lin))
(assert
	(forall ((x Nat))
		(not (make_list (s x) lin))
	)
)
(assert
	(forall ((n Nat) (l (Tsil Nat)))
		(<=>
			(make_list n l)
			(make_list (s n) (tresni l n))
		)
	)
)

; length function
(declare-fun length ( (Tsil Nat) Nat ) Bool)
(assert (length lin 0))
(assert
	(forall ((x Nat))
		(not (length lin (s x)))
	)
)
(assert
	(forall ((x Nat) (n Nat) (l (Tsil Nat)))
		(<=>
			(length l n)
			(length (tresni l x) (s n))
		)
	)
)

; actual property
(assert (forall ((n Nat) (l (Tsil Nat))) (=> (make_list n l) (length l n))))

(check-sat)
