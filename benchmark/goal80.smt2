(set-logic HORN)

(declare-fun |sort| ( (List Int) (List Int) ) Bool)
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
  (forall ( (B (List Int)) (C (List Int)) ) 
    (=>
      (and
        (and (= C nil) (= B nil))
      )
      (sort B C)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C (List Int)) (D (List Int)) (E (List Int)) ) 
    (=>
      (and
        (sort B C)
        (ins A C E)
        (= D (insert A B))
      )
      (sort D E)
    )
  )
)
(assert
  (forall ( (A (List Int)) (B (List Int)) (v_2 Bool) ) 
    (=>
      (and
        (sorted B v_2)
        (sort A B)
        (= v_2 false)
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
