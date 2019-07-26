(set-logic HORN)

(declare-datatypes ( (Pair 2) ) (
  (par (T1 T2) (
    (mk-pair (first T1) (second T2))
  ))
))

(declare-fun |zip| ( (List Int) (List Int) (List (Pair Int Int)) ) Bool)
(declare-fun |incorrect| ( ) Bool)
(declare-fun |rev| ( (List Int) (List Int) ) Bool)
(declare-fun |len| ( (List Int) Int ) Bool)
(declare-fun |zappend| ( (List (Pair Int Int)) (List (Pair Int Int)) (List (Pair Int Int)) ) Bool)
(declare-fun |zrev| ( (List (Pair Int Int)) (List (Pair Int Int)) ) Bool)
(declare-fun |append| ( (List Int) (List Int) (List Int) ) Bool)

(assert
  (forall ( (A (List Int)) (B (List Int)) (v_2 (List Int)) ) 
    (=>
      (and
        (and (= A nil) (= v_2 B))
      )
      (append A B v_2)
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
  (forall ( (G (List (Pair Int Int))) (H (List (Pair Int Int))) (v_2 (List (Pair Int Int))) ) 
    (=>
      (and
        (and (= G nil) (= v_2 H))
      )
      (zappend G H v_2)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (List (Pair Int Int))) (D (List (Pair Int Int))) (E (List (Pair Int Int))) (F (List (Pair Int Int))) (G (List (Pair Int Int))) ) 
    (=>
      (and
        (zappend C F D)
        (and (= G (insert (mk-pair A B) D)) (= E (insert (mk-pair A B) C)))
      )
      (zappend E F G)
    )
  )
)
(assert
  (forall ( (A (List Int)) (B (List Int)) ) 
    (=>
      (and
        (and (= B nil) (= A nil))
      )
      (rev A B)
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
  (forall ( (G (List (Pair Int Int))) (H (List (Pair Int Int))) ) 
    (=>
      (and
        (and (= H nil) (= G nil))
      )
      (zrev G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C (List (Pair Int Int))) (D (List (Pair Int Int))) (E (List (Pair Int Int))) (F (List (Pair Int Int))) (G (List (Pair Int Int))) ) 
    (=>
      (and
        (zappend D E G)
        (zrev C D)
        (and (= F (insert (mk-pair A B) C)) (= E (insert (mk-pair A B) nil)))
      )
      (zrev F G)
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
  (forall ( (A (List Int)) (B (List Int)) (G (List (Pair Int Int))) ) 
    (=>
      (and
        (and (= A nil) (= G nil))
      )
      (zip A B G)
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
  (forall ( (A (List Int)) (B Int) (C (List Int)) (D (List Int)) (E (List Int)) (F (List (Pair Int Int))) (G (List (Pair Int Int))) (H (List (Pair Int Int))) ) 
    (=>
      (and
        (zrev G H)
        (len A B)
        (rev A D)
        (zip A C G)
        (len C B)
        (rev C E)
        (zip D E F)
        (not (= F H))
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
