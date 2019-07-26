(set-logic HORN)

(declare-fun |last| ( (List Int) Int ) Bool)
(declare-fun |incorrect| ( ) Bool)

(assert
  (forall ( (A (List Int)) (B Int) ) 
    (=>
      (and
        (and (= A nil) (= B 0))
      )
      (last A B)
    )
  )
)
(assert
  (forall ( (A (List Int)) (F Int) ) 
    (=>
      (and
        (= A (insert F nil))
      )
      (last A F)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C Int) ) 
    (=>
      (and
        (last B C)
        (and (= B (insert A nil)) (not (= C A)))
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
