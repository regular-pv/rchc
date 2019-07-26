(set-logic HORN)

(declare-fun |incorrect| ( ) Bool)
(declare-fun |count| ( Int (List Int) Int ) Bool)
(declare-fun |append| ( (List Int) (List Int) (List Int) ) Bool)

(assert
  (forall ( (A (List Int)) (B (List Int)) (v_2 (List Int)) ) 
    (=>
      (and
        (and (= A nil) (= v_2 B))
      )
      (append A B v_2)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C (List Int)) (D (List Int)) (E (List Int)) (F (List Int)) ) 
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
  (forall ( (A Int) (B (List Int)) (C Int) ) 
    (=>
      (and
        (and (= B nil) (= C 0))
      )
      (count A B C)
    )
  )
)
(assert
  (forall ( (A (List Int)) (B Int) (C Int) (D (List Int)) (E Int) ) 
    (=>
      (and
        (count C A B)
        (and (= D (insert C A)) (>= B 0) (= E (+ 1 B)))
      )
      (count C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C Int) (D (List Int)) (E Int) ) 
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
  (forall ( (A (List Int)) (B (List Int)) (C Int) (D Int) (E (List Int)) (F Int) ) 
    (=>
      (and
        (count D E F)
        (append B A E)
        (count D B C)
        (and (>= C (+ 1 F)) (>= F 0) (>= C 0))
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
