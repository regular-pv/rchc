(set-logic HORN)

(declare-fun |drop| ( Int (List Int) (List Int) ) Bool)
(declare-fun |incorrect| ( ) Bool)
(declare-fun |diff_list| ( (List Int) (List Int) ) Bool)

(assert
  (forall ( (A Int) (B (List Int)) (C (List Int)) ) 
    (=>
      (and
        (and (= C nil) (= B nil))
      )
      (drop A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C Int) (D (List Int)) (E (List Int)) ) 
    (=>
      (and
        (and (= D (insert A B)) (= E (insert A B)) (= C 0))
      )
      (drop C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (List Int)) (D Int) (E (List Int)) (F (List Int)) ) 
    (=>
      (and
        (drop B C F)
        (and (= D (+ 1 B)) (= E (insert A C)) (not (= D 0)))
      )
      (drop D E F)
    )
  )
)
(assert
  (forall ( (A (List Int)) (B (List Int)) (v_2 Int) ) 
    (=>
      (and
        (diff_list A B)
        (drop v_2 B A)
        (= 0 v_2)
      )
      incorrect
    )
  )
)
(assert
  (forall ( (A (List Int)) (B Int) (C (List Int)) (v_3 (List Int)) ) 
    (=>
      (and
        (and (= A (insert B C)) (= v_3 nil))
      )
      (diff_list v_3 A)
    )
  )
)
(assert
  (forall ( (A (List Int)) (B Int) (C (List Int)) (v_3 (List Int)) ) 
    (=>
      (and
        (and (= A (insert B C)) (= v_3 nil))
      )
      (diff_list A v_3)
    )
  )
)
(assert
  (forall ( (A (List Int)) (B (List Int)) (C Int) (D (List Int)) (E Int) (F (List Int)) ) 
    (=>
      (and
        (and (= A (insert E F)) (= B (insert C D)) (not (= C E)))
      )
      (diff_list B A)
    )
  )
)
(assert
  (forall ( (A (List Int)) (B (List Int)) (C (List Int)) (D Int) (E (List Int)) ) 
    (=>
      (and
        (diff_list C E)
        (and (= A (insert D E)) (= B (insert D C)))
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
