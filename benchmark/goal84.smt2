(set-logic HORN)

(declare-datatypes ( (Pair 2) ) (
  (par (T1 T2) (
    (mk-pair (first T1) (second T2))
  ))
))

(declare-fun |zip| ( (List Int) (List Int) (List (Pair Int Int)) ) Bool)
(declare-fun |incorrect| ( ) Bool)
(declare-fun |ztake| ( Int (List (Pair Int Int)) (List (Pair Int Int)) ) Bool)
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
  (forall ( (A Int) (H (List (Pair Int Int))) (I (List (Pair Int Int))) ) 
    (=>
      (and
        (and (= I nil) (= H nil))
      )
      (ztake A H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (List (Pair Int Int))) (D Int) (E (List (Pair Int Int))) (F (List (Pair Int Int))) ) 
    (=>
      (and
        (and (= F nil) (= D 0) (= E (insert (mk-pair A B) C)))
      )
      (ztake D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D (List (Pair Int Int))) (E (List (Pair Int Int))) (F Int) (G (List (Pair Int Int))) (H (List (Pair Int Int))) ) 
    (=>
      (and
        (ztake C D E)
        (and (= H (insert (mk-pair A B) E))
     (not (= F 0))
     (= F (+ 1 C))
     (= G (insert (mk-pair A B) D)))
      )
      (ztake F G H)
    )
  )
)
(assert
  (forall ( (B (List Int)) (C (List Int)) (H (List (Pair Int Int))) ) 
    (=>
      (and
        (and (= B nil) (= H nil))
      )
      (zip B C H)
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
        (ztake D A B)
        (take D C F)
        (take D E G)
        (not (= B H))
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
