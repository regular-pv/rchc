(set-logic HORN)

(declare-fun |incorrect| ( ) Bool)
(declare-fun |mem| ( Int (List Int) Bool ) Bool)
(declare-fun |append| ( (List Int) (List Int) (List Int) ) Bool)

(assert
  (forall ( (A Int) (B (List Int)) (v_2 Bool) ) 
    (=>
      (and
        (and (= B nil) (= v_2 false))
      )
      (mem A B v_2)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C Int) (D (List Int)) (v_4 Bool) (v_5 Bool) ) 
    (=>
      (and
        (mem C B v_4)
        (and (= v_4 true) (= D (insert A B)) (= v_5 true))
      )
      (mem C D v_5)
    )
  )
)
(assert
  (forall ( (A (List Int)) (B Int) (C (List Int)) (v_3 Bool) (v_4 Bool) ) 
    (=>
      (and
        (mem B A v_3)
        (and (= v_3 false) (= C (insert B A)) (= v_4 true))
      )
      (mem B C v_4)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C Int) (D (List Int)) (v_4 Bool) (v_5 Bool) ) 
    (=>
      (and
        (mem C B v_4)
        (and (= v_4 false) (= D (insert A B)) (not (= C A)) (= v_5 false))
      )
      (mem C D v_5)
    )
  )
)
(assert
  (forall ( (B (List Int)) (C (List Int)) (v_2 (List Int)) ) 
    (=>
      (and
        (and (= B nil) (= v_2 C))
      )
      (append B C v_2)
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
  (forall ( (A (List Int)) (B (List Int)) (C Int) (D (List Int)) (v_4 Bool) (v_5 Bool) ) 
    (=>
      (and
        (mem C D v_4)
        (append B A D)
        (mem C B v_5)
        (and (= v_4 false) (= v_5 true))
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
