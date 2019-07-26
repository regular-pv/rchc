(set-logic HORN)

(declare-fun |ins1| ( Int (List Int) (List Int) ) Bool)
(declare-fun |mem| ( Int (List Int) Bool ) Bool)
(declare-fun |incorrect| ( ) Bool)

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
  (forall ( (A Int) (B (List Int)) (C (List Int)) ) 
    (=>
      (and
        (and (= C (insert A nil)) (= B nil))
      )
      (ins1 A B C)
    )
  )
)
(assert
  (forall ( (A (List Int)) (B Int) (C (List Int)) (D (List Int)) ) 
    (=>
      (and
        (and (= D (insert B A)) (= C (insert B A)))
      )
      (ins1 B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C (List Int)) (D Int) (E (List Int)) (F (List Int)) ) 
    (=>
      (and
        (ins1 D B C)
        (and (= E (insert A B)) (= F (insert A C)) (not (= D A)))
      )
      (ins1 D E F)
    )
  )
)
(assert
  (forall ( (A (List Int)) (B Int) (C (List Int)) (v_3 Bool) ) 
    (=>
      (and
        (mem B C v_3)
        (ins1 B A C)
        (= v_3 false)
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
