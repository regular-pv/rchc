(set-logic HORN)

(declare-fun diff_list ( (List Nat) (List Nat) ) Bool)

(assert
  (forall ( (B Nat) (C (List Nat)) )
    (diff_list nil (insert B C))
  )
)
(assert
  (forall ( (B Nat) (C (List Nat)) )
    (diff_list (insert B C) nil)
  )
)
(assert
  (forall ( (C Nat) (D (List Nat)) (E Nat) (F (List Nat)) )
    (=>
      (and
        (not (= C E))
      )
      (diff_list (insert C D) (insert E F))
    )
  )
)
(assert
  (forall ( (C (List Nat)) (D Nat) (E (List Nat)) )
    (=>
      (and
        (diff_list C E)
      )
      (diff_list (insert D C) (insert D E))
    )
  )
)
(assert
  (forall ((A (List Nat)) (B (List Nat))) (not (and (diff_list A B) (= A B))))
  )

(check-sat)
