(set-logic HORN)

(declare-fun |drop| ( Int (List Int) (List Int) ) Bool)
(declare-fun |incorrect| ( ) Bool)
(declare-fun |minus| ( Int Int Int ) Bool)
(declare-fun |len| ( (List Int) Int ) Bool)

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
  (forall ( (A (List Int)) (B Int) (C (List Int)) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (minus D E F)
        (drop E C A)
        (len A B)
        (len C D)
        (and (>= B 0) (>= D 0) (>= E 0) (not (= B F)))
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
