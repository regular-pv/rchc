(set-logic HORN)

(declare-fun |sort| ( (List Int) (List Int) ) Bool)
(declare-fun |incorrect| ( ) Bool)
(declare-fun |ins| ( Int (List Int) (List Int) ) Bool)
(declare-fun |len| ( (List Int) Int ) Bool)

(assert
  (forall ( (A (List Int)) (B Int) ) 
    (=>
      (and
        (and (= B 0) (= A nil))
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
        (and (= E (+ 1 C)) (>= C 0) (= D (insert A B)))
      )
      (len D E)
    )
  )
)
(assert
  (forall ( (B Int) (A (List Int)) (C (List Int)) ) 
    (=>
      (and
        (and (= A nil) (= C (insert B nil)))
      )
      (ins B A C)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C Int) (D (List Int)) (E (List Int)) ) 
    (=>
      (and
        (and (= D (insert A B)) (<= C (+ (- 1) A)) (= E (insert C (insert A B))))
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
        (and (= E (insert A B)) (>= D A) (= F (insert A C)))
      )
      (ins D E F)
    )
  )
)
(assert
  (forall ( (A (List Int)) (B (List Int)) ) 
    (=>
      (and
        (and (= A nil) (= B nil))
      )
      (sort A B)
    )
  )
)
(assert
  (forall ( (A (List Int)) (B Int) (C (List Int)) (D (List Int)) (E (List Int)) ) 
    (=>
      (and
        (ins B C E)
        (sort A C)
        (= D (insert B A))
      )
      (sort D E)
    )
  )
)
(assert
  (forall ( (A (List Int)) (B Int) (C (List Int)) (D Int) ) 
    (=>
      (and
        (len C D)
        (sort C A)
        (len A B)
        (and (>= B 0) (>= D 0) (not (= B D)))
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
