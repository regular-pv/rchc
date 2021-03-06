(set-logic HORN)

(declare-fun |incorrect| ( ) Bool)
(declare-fun |ins| ( Int (List Int) (List Int) ) Bool)
(declare-fun |sorted| ( (List Int) Bool ) Bool)

(assert
  (forall ( (A Int) (B (List Int)) (C (List Int)) ) 
    (=>
      (and
        (and (= C (insert A nil)) (= B nil))
      )
      (ins A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C Int) (D (List Int)) (E (List Int)) ) 
    (=>
      (and
        (and (= E (insert C (insert A B))) (<= C (+ (- 1) A)) (= D (insert A B)))
      )
      (ins C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C (List Int)) (D Int) (E (List Int)) (F (List Int)) ) 
    (=>
      (and
        (ins D B C)
        (and (= F (insert A C)) (>= D A) (= E (insert A B)))
      )
      (ins D E F)
    )
  )
)
(assert
  (forall ( (B (List Int)) (v_1 Bool) ) 
    (=>
      (and
        (and (= B nil) (= v_1 true))
      )
      (sorted B v_1)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (v_2 Bool) ) 
    (=>
      (and
        (and (= B (insert A nil)) (= v_2 true))
      )
      (sorted B v_2)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (List Int)) (D (List Int)) (E (List Int)) (v_5 Bool) (v_6 Bool) ) 
    (=>
      (and
        (sorted D v_5)
        (and (= v_5 true) (= E (insert A D)) (<= A B) (= D (insert B C)) (= v_6 true))
      )
      (sorted E v_6)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (List Int)) (D (List Int)) (E (List Int)) (v_5 Bool) (v_6 Bool) ) 
    (=>
      (and
        (sorted D v_5)
        (and (= v_5 true)
     (= E (insert A D))
     (>= A (+ 1 B))
     (= D (insert B C))
     (= v_6 false))
      )
      (sorted E v_6)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (List Int)) (D (List Int)) (E (List Int)) (v_5 Bool) (v_6 Bool) ) 
    (=>
      (and
        (sorted D v_5)
        (and (= v_5 false) (= E (insert A D)) (= D (insert B C)) (= v_6 false))
      )
      (sorted E v_6)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C (List Int)) (v_3 Bool) (v_4 Bool) ) 
    (=>
      (and
        (sorted C v_3)
        (ins A B C)
        (sorted B v_4)
        (and (= v_3 false) (= v_4 true))
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
(get-model)
(exit)
