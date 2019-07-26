(set-logic HORN)

(declare-fun |incorrect| ( ) Bool)
(declare-fun |count| ( Int (List Int) Int ) Bool)
(declare-fun |append| ( (List Int) (List Int) (List Int) ) Bool)
(declare-fun |rev| ( (List Int) (List Int) ) Bool)

(assert
  (forall ( (A Int) (B (List Int)) (C Int) ) 
    (=>
      (and
        (and (= C 0) (= B nil))
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
        (and (= E (+ 1 B)) (>= B 0) (= D (insert C A)))
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
        (and (not (= C A)) (>= E 0) (= D (insert A B)))
      )
      (count C D E)
    )
  )
)
(assert
  (forall ( (B (List Int)) (D (List Int)) (v_2 (List Int)) ) 
    (=>
      (and
        (and (= B nil) (= v_2 D))
      )
      (append B D v_2)
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
  (forall ( (B (List Int)) (D (List Int)) ) 
    (=>
      (and
        (and (= D nil) (= B nil))
      )
      (rev B D)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C (List Int)) (D (List Int)) (E (List Int)) (F (List Int)) ) 
    (=>
      (and
        (append C D F)
        (rev B C)
        (and (= E (insert A B)) (= D (insert A nil)))
      )
      (rev E F)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C Int) (D (List Int)) (E Int) ) 
    (=>
      (and
        (count C D E)
        (count C B A)
        (rev B D)
        (and (>= A 0) (>= E 0) (not (= A E)))
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
