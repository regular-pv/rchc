(set-logic HORN)

(declare-fun count ( Nat (List Nat) Nat ) Bool)
(declare-fun append ( (List Nat) (List Nat) (List Nat) ) Bool)

(assert
  (forall ( (A (List Nat)) (B (List Nat)) (v_2 (List Nat)) )
    (=>
      (and
        (and (= A nil) (= v_2 B))
      )
      (append A B v_2)
    )
  )
)
(assert
  (forall ( (A Nat) (B (List Nat)) (C (List Nat)) (D (List Nat)) (E (List Nat)) (F (List Nat)) )
    (=>
      (and
        (append B E C)
        (and (= F (insert A C)) (= D (insert A B)))
      )
      (append D E F)
    )
  )
)
(assert
  (forall ( (A Nat) (B (List Nat)) (C Nat) )
    (=>
      (and
        (and (= B nil) (= C 0))
      )
      (count A B C)
    )
  )
)
(assert
  (forall ( (A (List Nat)) (B Nat) (C Nat) (D (List Nat)) (E Nat) )
    (=>
      (and
        (count C A B)
        (and (= D (insert C A)) (>= B 0) (= E (s B)))
      )
      (count C D E)
    )
  )
)
(assert
  (forall ( (A Nat) (B (List Nat)) (C Nat) (D (List Nat)) (E Nat) )
    (=>
      (and
        (count C B E)
        (and (= D (insert A B)) (>= E 0) (not (= C A)))
      )
      (count C D E)
    )
  )
)
(assert
  (forall ( (A (List Nat)) (B (List Nat)) (C Nat) (D Nat) (E (List Nat)) (F Nat) )
    (not
      (and
        (count D E F)
        (append B A E)
        (count D B C)
        (and (>= C (s F)) (>= F 0) (>= C 0))
      )
    )
  )
)

(check-sat)
(exit)
