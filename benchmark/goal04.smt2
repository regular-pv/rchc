(set-logic HORN)

(declare-fun incorrect ( ) Bool)
(declare-fun count ( Nat (List Nat) Nat ) Bool)

(assert
  (forall ( (A Nat) (B (List Nat)) (C Nat) )
    (=>
      (and
        (and (= C 0) (= B nil))
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
        (and (= E (+ 1 B)) (>= B 0) (= D (insert C A)))
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
        (and (not (= C A)) (>= E 0) (= D (insert A B)))
      )
      (count C D E)
    )
  )
)
(assert
  (forall ( (A (List Nat)) (B Nat) (C Nat) (D (List Nat)) (E Nat) )
    (=>
      (and
        (count C D E)
        (count C A B)
        (and (not (= B (+ (- 1) E))) (>= B 0) (>= E 0) (= D (insert C A)))
      )
      incorrect
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) )
    (=>
      (and
        incorrect
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
