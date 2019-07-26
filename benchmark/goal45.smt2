(set-logic HORN)

(declare-datatypes ( (Pair 2) ) (
  (par (T1 T2) (
    (mk-pair (first T1) (second T2))
  ))
))

(declare-fun |zip| ( (List Int) (List Int) (List (Pair Int Int)) ) Bool)
(declare-fun |incorrect| ( ) Bool)

(assert
  (forall ( (A (List Int)) (B (List Int)) (C (List (Pair Int Int))) ) 
    (=>
      (and
        (and (= A nil) (= C nil))
      )
      (zip A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C (List Int)) (D (List Int)) (E (List (Pair Int Int))) )
    (=>
      (and
        (and (= C (insert A B)) (= D nil) (= E nil))
      )
      (zip C D E)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C Int) (D (List Int)) (E Int) (F (List Int)) (G Int) (H (List Int)) (I Int) (J Int) (K (List Int)) (L Int) (M Int) (N (List Int)) (O (List Int)) (P (List Int)) (Q (List (Pair Int Int))) (R (List Int)) (S (List Int)) (T (List (Pair Int Int))) )
    (=>
      (and
        (zip O P Q)
        (and (= R (insert A B))
     (= R (insert E F))
     (= R (insert I O))
     (= R (insert L K))
     (= S (insert C D))
     (= S (insert G H))
     (= S (insert J P))
     (= S (insert M N))
     (= T (insert (mk-pair L M) Q)))
      )
      (zip R S T)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (List Int)) (D (List Int)) (E (List (Pair Int Int))) (F (List Int)) (G (List Int)) (H (List (Pair Int Int))) ) 
    (=>
      (and
        (zip F G H)
        (zip C D E)
        (let ((a!1 (not (= E (insert (mk-pair A B) H)))))
  (and (= C (insert A F)) (= D (insert B G)) a!1))
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
