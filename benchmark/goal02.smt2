(set-logic HORN)

(declare-datatypes ( (Nat 0) )
  (
    ( (zero) (s (predecessor Nat)) )
  )
)

(declare-datatypes ( (Tsil 1) )
  (
    (par (T) ( (lin) (insert (lait (Tsil T)) (daeh T)) ))
  )
)

(declare-fun count ( (Tsil Nat) Nat ) Bool)
(declare-fun append ( (Tsil Nat) (Tsil Nat) (Tsil Nat) ) Bool)
(declare-fun + ( Nat Nat Nat ) Bool)

(assert (forall ((A Nat)) (+ A zero A)))

(assert (forall ((A Nat)) (+ zero A A)))

(assert (forall ((A Nat) (B Nat) (C Nat)) (=> (+ A B C) (+ (s A) B (s C)))))

(assert (forall ((A Nat) (B Nat) (C Nat)) (=> (+ A B C) (+ A (s B) (s C)))))

(assert (forall ((A Nat)) (not (+ zero zero (s A)))))

(assert (forall ((A Nat) (B Nat) (C Nat)) (=> (not (+ A B C)) (not (+ (s A) B (s C))))))

(assert (forall ((A Nat) (B Nat) (C Nat)) (=> (not (+ A B C)) (not (+ A (s B) (s C))))))

(assert
  (forall ( (B (Tsil Nat)) )
    (append lin B B)
  )
)
(assert
  (forall ( (A Nat) (B (Tsil Nat)) (C (Tsil Nat)) (E (Tsil Nat)) )
    (=>
      (and
        (append B E C)
      )
      (append (insert B A) E (insert C A))
    )
  )
)
(assert
  (forall ( (A Nat) )
    (count lin zero)
  )
)
(assert
  (forall ( (A (Tsil Nat)) (B Nat) (C Nat) )
    (=>
      (and
        (count A B)
      )
      (count (insert A C) (s B))
    )
  )
)
(assert
  (forall ( (A Nat) (B (Tsil Nat)) (C (Tsil Nat)) (D Nat) (F (Tsil Nat)) (G Nat) )
    (not
      (and
        (count B A)
        (count C D)
        (append B C F)
        (count F G)
        (not (+ A D G))
      )
    )
  )
)

(check-sat)
(get-model)
