; from Tons Of Inductive Problems
; property: x#xs ≠ xs
(assert
	(forall ((x Nat) (xs (List Nat))) (!= (insert x xs) xs))
)
(check-sat)
