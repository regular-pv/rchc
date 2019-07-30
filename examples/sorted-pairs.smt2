(set-logic HORN)

(declare-datatypes ( (List 1) )
  (
    (par (T) ( (nil) (insert (head T) (tail (List T))) ))
  )
)

(declare-datatypes ( (Pair 1) )
  (
    (par (T) ( (pair (left T) (right T) ) ))
  )
)

(declare-datatypes ( (AB 0) )
  (
    ( (a) (b) )
  )
)

(declare-fun all_b ( (List AB) ) Bool) ; needed to define `sorted`
(declare-fun sorted ( (List AB) ) Bool) ; sorted lists
(declare-fun sorted_pair ( (Pair (List AB)) ) Bool) ; sorted lists

(assert
  (forall ( (l (List AB)) ) (=> (all_b l) (all_b (insert b l)) ) )
)
(assert
  (all_b nil)
)

(assert
  (forall ( (l (List AB)) ) (=> (sorted l) (sorted (insert a l)) ) )
)
(assert
  (forall ( (l (List AB)) ) (=> (all_b l) (sorted (insert b l)) ) )
)
(assert
  (sorted nil)
)
(assert
  (forall ( (l (List AB)) ) (not (sorted (insert b (insert a l)))))
)

(assert
  (forall ( (l1 (List AB)) (l2 (List AB)) )
    (=>
      (and
        (sorted l1)
        (sorted l2)
      )
      (sorted_pair (pair l1 l2))
    )
  )
)

(assert
  (forall ( (l1 (List AB)) (l2 (List AB)) )
    (=>
      (sorted_pair (pair l1 l2))
      (sorted l1)
    )
  )
)

(assert
  (forall ( (l1 (List AB)) (l2 (List AB)) )
    (=>
      (sorted_pair (pair l1 l2))
      (sorted l2)
    )
  )
)

(assert
  (forall ( (l1 (List AB)) (l2 (List AB)) )
    (not
      (and
        (not (sorted l1))
        (sorted_pair (pair l1 l2))
      )
    )
  )
)

(assert
  (forall ( (l1 (List AB)) (l2 (List AB)) )
    (not
      (and
        (not (sorted l2))
        (sorted_pair (pair l1 l2))
      )
    )
  )
)

(check-sat)
(get-model)
