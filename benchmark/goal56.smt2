(set-logic HORN)

(declare-fun |incorrect| ( ) Bool)
(declare-fun |minus| ( Int Int Int ) Bool)
(declare-fun |diff_list| ( (List Int) (List Int) ) Bool)
(declare-fun |len| ( (List Int) Int ) Bool)
(declare-fun |drop| ( Int (List Int) (List Int) ) Bool)
(declare-fun |append| ( (List Int) (List Int) (List Int) ) Bool)

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
  (forall ( (A Int) (B (List Int)) (C (List Int)) ) 
    (=>
      (and
        (and (= B nil) (= C nil))
      )
      (drop A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C Int) (D (List Int)) (E (List Int)) ) 
    (=>
      (and
        (and (= D (insert A B)) (= C 0) (= E (insert A B)))
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
        (and (not (= D 0)) (= D (+ 1 B)) (= E (insert A C)))
      )
      (drop D E F)
    )
  )
)
(assert
  (forall ( (D (List Int)) (E (List Int)) (v_2 (List Int)) ) 
    (=>
      (and
        (and (= D nil) (= v_2 E))
      )
      (append D E v_2)
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
  (forall ( (A (List Int)) (B (List Int)) (C (List Int)) (D Int) (E Int) (F Int) (G (List Int)) (H (List Int)) (I (List Int)) (J (List Int)) ) 
    (=>
      (and
        (diff_list I J)
        (append B C A)
        (drop D A I)
        (drop D B G)
        (len B E)
        (drop F C H)
        (minus D E F)
        (append G H J)
        (and (>= E 0) (>= D 0))
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
(exit)
