(set-logic HORN)

(declare-fun |sort| ( (List Int) (List Int) ) Bool)
(declare-fun |incorrect| ( ) Bool)
(declare-fun |count| ( Int (List Int) Int ) Bool)
(declare-fun |ins| ( Int (List Int) (List Int) ) Bool)

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
  (forall ( (A Int) (B (List Int)) (D (List Int)) ) 
    (=>
      (and
        (and (= B nil) (= D (insert A nil)))
      )
      (ins A B D)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C Int) (D (List Int)) (E (List Int)) ) 
    (=>
      (and
        (and (= D (insert A B)) (<= C (+ (- 1) A)) (= E (insert C D)))
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
  (forall ( (A Int) (B (List Int)) (C Int) (D (List Int)) (E Int) ) 
    (=>
      (and
        (count C D E)
        (count C B A)
        (sort B D)
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
