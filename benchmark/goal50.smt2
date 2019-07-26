(set-logic HORN)

(declare-fun |incorrect| ( ) Bool)
(declare-fun |minus| ( Int Int Int ) Bool)
(declare-fun |diff_list| ( (List Int) (List Int) ) Bool)
(declare-fun |len| ( (List Int) Int ) Bool)
(declare-fun |butlast| ( (List Int) (List Int) ) Bool)
(declare-fun |take| ( Int (List Int) (List Int) ) Bool)

(assert
  (forall ( (A Int) (B (List Int)) (C (List Int)) ) 
    (=>
      (and
        (and (= C nil) (= B nil))
      )
      (take A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C Int) (D (List Int)) (E (List Int)) ) 
    (=>
      (and
        (and (= D (insert A B)) (= E nil) (= C 0))
      )
      (take C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (List Int)) (D (List Int)) (E Int) (F (List Int)) (G (List Int)) ) 
    (=>
      (and
        (take B C D)
        (and (= E (+ 1 B)) (= F (insert A C)) (= G (insert A D)) (not (= E 0)))
      )
      (take E F G)
    )
  )
)
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
  (forall ( (A Int) (D Int) (G Int) ) 
    (=>
      (and
        (and (>= A (+ 1 D)) (= A (+ G D)))
      )
      (minus A D G)
    )
  )
)
(assert
  (forall ( (A (List Int)) (B Int) ) 
    (=>
      (and
        (and (= A nil) (= B 0))
      )
      (len A B)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C Int) (D (List Int)) (E Int) ) 
    (=>
      (and
        (len B C)
        (and (= D (insert A B)) (= E (+ 1 C)))
      )
      (len D E)
    )
  )
)
(assert
  (forall ( (B (List Int)) (C (List Int)) ) 
    (=>
      (and
        (and (= C nil) (= B nil))
      )
      (butlast B C)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C (List Int)) ) 
    (=>
      (and
        (and (= C nil) (= B (insert A nil)))
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
        (and (= v_5 nil) (= E (insert A B)) (= D (insert A C)))
      )
      (butlast D E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (List Int)) (D (List Int)) (E (List Int)) (v_5 Int) ) 
    (=>
      (and
        (diff_list D E)
        (butlast C D)
        (len C A)
        (minus A v_5 B)
        (take B C E)
        (= 1 v_5)
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
        (and (= B (insert C D)) (= A (insert E F)) (not (= C E)))
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
(exit)
