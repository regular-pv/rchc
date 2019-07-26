(set-logic HORN)

(declare-datatypes ( (Pair 2) ) (
  (par (T1 T2) (
    (mk-pair (first T1) (second T2))
  ))
))

(declare-fun |zdrop| ( Int (List (Pair Int Int)) (List (Pair Int Int)) ) Bool)
(declare-fun |zip| ( (List Int) (List Int) (List (Pair Int Int)) ) Bool)
(declare-fun |drop| ( Int (List Int) (List Int) ) Bool)
(declare-fun |incorrect| ( ) Bool)

(assert
  (forall ( (A Int) (B (List Int)) (C (List Int)) ) 
    (=>
      (and
        (and (= C nil) (= B nil))
      )
      (drop A B C)
    )
  )
)
(assert
  (forall ( (A Int) (B (List Int)) (C Int) (D (List Int)) (E (List Int)) ) 
    (=>
      (and
        (and (= D (insert A B)) (= E (insert A B)) (= C 0))
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
        (and (= D (+ 1 B)) (= E (insert A C)) (not (= D 0)))
      )
      (drop D E F)
    )
  )
)
(assert
  (forall ( (A Int) (G (List (Pair Int Int))) (H (List (Pair Int Int))) ) 
    (=>
      (and
        (and (= H nil) (= G nil))
      )
      (zdrop A G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (List (Pair Int Int))) (D Int) (E (List (Pair Int Int))) (F (List (Pair Int Int))) ) 
    (=>
      (and
        (and (= F (insert (mk-pair A B) C)) (= D 0) (= E (insert (mk-pair A B) C)))
      )
      (zdrop D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (List (Pair Int Int))) (E Int) (F (List (Pair Int Int))) (G (List (Pair Int Int))) ) 
    (=>
      (and
        (zdrop C D G)
        (and (not (= E 0)) (= E (+ 1 C)) (= F (insert (mk-pair A B) D)))
      )
      (zdrop E F G)
    )
  )
)
(assert
  (forall ( (B (List Int)) (C (List Int)) (G (List (Pair Int Int))) ) 
    (=>
      (and
        (and (= B nil) (= G nil))
      )
      (zip B C G)
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
  (forall ( (A (List (Pair Int Int))) (B (List (Pair Int Int))) (C (List Int)) (D Int) (E (List Int)) (F (List Int)) (G (List Int)) (H (List (Pair Int Int))) ) 
    (=>
      (and
        (zip F G H)
        (zip C E A)
        (zdrop D A B)
        (drop D C F)
        (drop D E G)
        (and (>= D 0) (not (= B H)))
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
