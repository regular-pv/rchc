; from Tons Of Inductive Problems
; property: length (rev xs) = length xs

; rev nil -> nil
; rev x::l -> push_back x (rev l)

(declare-fun len_eq ( (List Nat) (List Nat) ) Bool) ; exact

(assert
	(len_eq nil nil)
)
(assert
	(forall ((x Nat) (l1 (List Nat))) (not (len_eq (insert x l1) nil)))
)
(assert
	(forall ((y Nat) (l2 (List Nat))) (not (len_eq nil (insert y l2))))
)
(assert
	(forall ((x Nat) (y Nat) (l1 (List Nat)) (l2 (List Nat))) (<=> (len_eq l1 l2) (len_eq (insert x l1) (insert y l2))))
)

(declare-fun push_back ( Nat (List Nat) (List Nat) ) Bool) ; over-approx

(assert
	(forall ((x Nat)) (push_back x nil (insert x nil)))
)
(assert
	(forall ((x Nat) (y Nat) (l1 (List Nat)) (l2 (List Nat)))
		(=>
			(push_back x l1 l2)
			(push_back x (insert y l1) (insert y l2))
		)
	)
)

(declare-fun rev ( (List Nat) (List Nat) ) Bool) ; over-approx

(assert
	(rev nil nil)
)
(assert
	(forall ((x Nat) (l1 (List Nat)) (l2 (List Nat)) (l3 (List Nat)))
		(=>
			(and (rev l1 l2) (push_back x l2 l3))
			(rev (insert x l1) l3)
		)
	)
)

; actual property
(assert
	(forall ((xs (List Nat)) (l (List Nat)))
		(=>
			(rev xs l)
			(len_eq xs l)
		)
	)
)

(check-sat)
