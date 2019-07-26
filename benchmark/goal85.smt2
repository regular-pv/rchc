(set-logic HORN)

(declare-datatypes ( (Pair 2) ) (
  (par (T1 T2) (
    (mk-pair (first T1) (second T2))
  ))
))

(declare-fun |zip| ( (List Int) (List Int) (List (Pair Int Int)) ) Bool)
(declare-fun |incorrect| ( ) Bool)
(declare-fun |len| ( (List Int) Int ) Bool)
(declare-fun |zappend| ( (List (Pair Int Int)) (List (Pair Int Int)) (List (Pair Int Int)) ) Bool)
(declare-fun |drop| ( Int (List Int) (List Int) ) Bool)
(declare-fun |append| ( (List Int) (List Int) (List Int) ) Bool)
(declare-fun |take| ( Int (List Int) (List Int) ) Bool)

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
        (and (= D (insert A B)) (>= C 0) (= E (+ 1 C)))
      )
      (len D E)
    )
  )
)
(assert
  (forall ( (D Int) (A (List Int)) (B (List Int)) ) 
    (=>
      (and
        (and (= B nil) (= A nil))
      )
      (take D A B)
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
  (forall ( (D Int) (A (List Int)) (B (List Int)) ) 
    (=>
      (and
        (and (= B nil) (= A nil))
      )
      (drop D A B)
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
  (forall ( (A (List Int)) (B (List (Pair Int Int))) (C (List Int)) (D (List Int)) (E (List Int)) (F (List (Pair Int Int))) (G (List (Pair Int Int))) (H Int) (I (List Int)) (J (List (Pair Int Int))) (K (List Int)) (L Int) ) 
    (=>
      (and
        (len K L)
        (append K C A)
        (zip A D B)
        (zip C E F)
        (take H D I)
        (drop L D E)
        (zappend J F G)
        (len K H)
        (zip K I J)
        (and (>= H 0) (>= L 0) (not (= B G)))
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
