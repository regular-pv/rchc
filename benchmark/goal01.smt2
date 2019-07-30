(set-logic HORN)

(declare-fun diff_list ( (List Nat) (List Nat) ) Bool)
(declare-fun drop ( Nat (List Nat) (List Nat) ) Bool)
(declare-fun append ( (List Nat) (List Nat) (List Nat) ) Bool)
(declare-fun take ( Nat (List Nat) (List Nat) ) Bool)

(assert
  (forall ( (A (List Nat)) (B (List Nat)) )
    (append nil B B)
  )
)
(assert
  (forall ( (A Nat) (B (List Nat)) (C (List Nat)) (E (List Nat)) )
    (=>
      (and
        (append B E C)
      )
      (append (insert A B) E (insert A C))
    )
  )
)



(assert
  (forall ( (F Nat) )
    (drop F nil nil)
  )
)
(assert
  (forall ( (A Nat) (B (List Nat)) )
    (drop 0 (insert A B) (insert A B))
  )
)
(assert
  (forall ( (A Nat) (B Nat) (C (List Nat)) (F (List Nat)) )
    (=>
      (and
        (drop B C F)
      )
      (drop (s B) (insert A C) F)
    )
  )
)



(assert
  (forall ( (F Nat) )
    (take F nil nil)
  )
)
(assert
  (forall ( (A Nat) (B (List Nat)) )
    (take 0 (insert A B) nil)
  )
)
(assert
  (forall ( (A Nat) (B Nat) (C (List Nat)) (D (List Nat)) )
    (=>
      (and
        (take B C D)
      )
      (take (s B) (insert A C) (insert A D))
    )
  )
)
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
  (forall ( (A Nat) (B (List Nat)) (C (List Nat)) (D (List Nat)) (E (List Nat)) )
    (not
      (and
        (not (= D E))
        (take A E B)
        (drop A E C)
        (append B C D)
      )
    )
  )
)

(check-sat)
(exit)
