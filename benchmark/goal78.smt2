(set-logic HORN)

(declare-fun |incorrect| ( ) Bool)
(declare-fun |count| ( Int (List Int) Int ) Bool)

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
  (forall ( (A Int) (B (List Int)) (C Int) (D (List Int)) (E Int) (F Int) (G (List Int)) (H Int) ) 
    (=>
      (and
        (count F G H)
        (count F B C)
        (count F D E)
        (and (= D (insert A nil))
     (= G (insert A B))
     (>= E 0)
     (>= C 0)
     (>= H 0)
     (not (= (+ C E) H)))
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
