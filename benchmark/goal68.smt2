(set-logic HORN)

(declare-fun |incorrect| ( ) Bool)
(declare-fun |minus| ( Int Int Int ) Bool)
(declare-fun |diff_list| ( (List Int) (List Int) ) Bool)
(declare-fun |len| ( (List Int) Int ) Bool)
(declare-fun |butlast| ( (List Int) (List Int) ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (and (<= A B) (= C 0))
      )
      (minus A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) ) 
    (=>
      (and
        (and (>= A (+ 1 B)) (= A (+ C B)))
      )
      (minus A B C)
    )
  )
)
(assert
  (forall ( (D (List Int)) (A Int) ) 
    (=>
      (and
        (and (= A 0) (= D nil))
      )
      (len D A)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C Int) (D (List Int)) (E Int) ) 
    (=>
      (and
        (len B C)
        (and (= E (+ 1 C)) (>= C 0) (= D (insert A B)))
      )
      (len D E)
    )
  )
)
(assert
  (forall ( (A (List Int)) (B (List Int)) ) 
    (=>
      (and
        (and (= A nil) (= B nil))
      )
      (butlast A B)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C (List Int)) ) 
    (=>
      (and
        (and (= B (insert A nil)) (= C nil))
      )
      (butlast B C)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C (List Int)) (D (List Int)) (E (List Int)) (v_5 (List Int)) ) 
    (=>
      (and
        (diff_list C v_5)
        (butlast C B)
        (and (= v_5 nil) (= D (insert A C)) (= E (insert A B)))
      )
      (butlast D E)
    )
  )
)
(assert
  (forall ( (A (List Int)) (B Int) (C (List Int)) (D Int) (E Int) (v_5 Int) ) 
    (=>
      (and
        (minus D v_5 E)
        (butlast C A)
        (len A B)
        (len C D)
        (and (= 1 v_5) (>= B 0) (>= D 0) (not (= B E)))
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
        (and (= A (insert E F)) (not (= C E)) (= B (insert C D)))
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

(get-model)

(exit)
