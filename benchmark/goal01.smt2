(set-logic HORN)

(declare-fun incorrect ( ) Bool)
(declare-fun diff_list ( (List Nat) (List Nat) ) Bool)
(declare-fun drop ( Nat (List Nat) (List Nat) ) Bool)
(declare-fun append ( (List Nat) (List Nat) (List Nat) ) Bool)
(declare-fun take ( Nat (List Nat) (List Nat) ) Bool)

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
  (forall ( (F Nat) (A (List Nat)) (B (List Nat)) )
    (=>
      (and
        (and (= B nil) (= A nil))
      )
      (drop F A B)
    )
  )
)
(assert
  (forall ( (A Nat) (B (List Nat)) (C Nat) (D (List Nat)) (E (List Nat)) )
    (=>
      (and
        (and (= D (insert A B)) (= E (insert A B)) (= C 0))
      )
      (drop C D E)
    )
  )
)
(assert
  (forall ( (A Nat) (B Nat) (C (List Nat)) (D Nat) (E (List Nat)) (F (List Nat)) )
    (=>
      (and
        (drop B C F)
        (and (= D (s B)) (= E (insert A C)) (not (= D 0)))
      )
      (drop D E F)
    )
  )
)
(assert
  (forall ( (F Nat) (A (List Nat)) (B (List Nat)) )
    (=>
      (and
        (and (= B nil) (= A nil))
      )
      (take F A B)
    )
  )
)
(assert
  (forall ( (A Nat) (B (List Nat)) (C Nat) (D (List Nat)) (E (List Nat)) )
    (=>
      (and
        (and (= D (insert A B)) (= E nil) (= C 0))
      )
      (take C D E)
    )
  )
)
(assert
  (forall ( (A Nat) (B Nat) (C (List Nat)) (D (List Nat)) (E Nat) (F (List Nat)) (G (List Nat)) )
    (=>
      (and
        (take B C D)
        (and (= E (s B)) (= F (insert A C)) (= G (insert A D)) (not (= E 0)))
      )
      (take E F G)
    )
  )
)
(assert
  (forall ( (A Nat) (B (List Nat)) (C (List Nat)) (D (List Nat)) (E (List Nat)) )
    (=>
      (and
        (diff_list D E)
        (take A E B)
        (drop A E C)
        (append B C D)
        true
      )
      incorrect
    )
  )
)
(assert
  (forall ( (A (List Nat)) (B Nat) (C (List Nat)) (v_3 (List Nat)) )
    (=>
      (and
        (and (= A (insert B C)) (= v_3 nil))
      )
      (diff_list v_3 A)
    )
  )
)
(assert
  (forall ( (A (List Nat)) (B Nat) (C (List Nat)) (v_3 (List Nat)) )
    (=>
      (and
        (and (= A (insert B C)) (= v_3 nil))
      )
      (diff_list A v_3)
    )
  )
)
(assert
  (forall ( (A (List Nat)) (B (List Nat)) (C Nat) (D (List Nat)) (E Nat) (F (List Nat)) )
    (=>
      (and
        (and (= B (insert C D)) (= A (insert E F)) (not (= C E)))
      )
      (diff_list B A)
    )
  )
)
(assert
  (forall ( (A (List Nat)) (B (List Nat)) (C (List Nat)) (D Nat) (E (List Nat)) )
    (=>
      (and
        (diff_list C E)
        (and (= B (insert D C)) (= A (insert D E)))
      )
      (diff_list B A)
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
