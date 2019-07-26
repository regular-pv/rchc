(set-logic HORN)

(declare-datatypes ( (Tree 1) ) (
  (par (A) (
    leaf
    (node (sel0 A) (sel1 (Tree A)) (sel2 (Tree A)))
  ))
))

(declare-fun |mirror| ( (Tree Int) (Tree Int) ) Bool)
(declare-fun |incorrect| ( ) Bool)
(declare-fun |nmax| ( Int Int Int ) Bool)
(declare-fun |height| ( (Tree Int) Int ) Bool)

(assert
  (forall ( (A (Tree Int)) (B (Tree Int)) ) 
    (=>
      (and
        (and (= B leaf) (= A leaf))
      )
      (mirror A B)
    )
  )
)
(assert
  (forall ( (A Int) (B (Tree Int)) (C (Tree Int)) (D (Tree Int)) (E (Tree Int)) (F (Tree Int)) (G (Tree Int)) ) 
    (=>
      (and
        (mirror D E)
        (mirror B C)
        (and (= G (node A C E)) (= F (node A D B)))
      )
      (mirror F G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Int) ) 
    (=>
      (and
        (and (<= A (+ (- 1) B)) (= v_2 B))
      )
      (nmax A B v_2)
    )
  )
)
(assert
  (forall ( (H Int) (G Int) (v_2 Int) ) 
    (=>
      (and
        (and (>= G H) (= v_2 G))
      )
      (nmax G H v_2)
    )
  )
)
(assert
  (forall ( (A (Tree Int)) (B Int) ) 
    (=>
      (and
        (and (= A leaf) (= B 0))
      )
      (height A B)
    )
  )
)
(assert
  (forall ( (A Int) (B (Tree Int)) (C Int) (D Int) (E (Tree Int)) (F Int) (G (Tree Int)) (H Int) ) 
    (=>
      (and
        (height E F)
        (height B C)
        (nmax C F D)
        (and (= G (node A B E)) (>= C 0) (>= F 0) (= H (+ 1 D)))
      )
      (height G H)
    )
  )
)
(assert
  (forall ( (A (Tree Int)) (B Int) (C Int) (D (Tree Int)) (E Int) ) 
    (=>
      (and
        (height D E)
        (height A B)
        (nmax B E C)
        (and (>= E 0) (<= C (- 2)) (>= B 0))
      )
      incorrect
    )
  )
)
(assert
  (forall ( (A (Tree Int)) (B Int) (C (Tree Int)) (D Int) ) 
    (=>
      (and
        (height C D)
        (mirror C A)
        (height A B)
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
