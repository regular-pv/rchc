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

(declare-fun split ( (List AB) (Pair (List AB)) ) Bool)
(declare-fun merge ( (Pair (List AB)) (List AB) ) Bool)
(declare-fun sort ( (List AB) (List AB) ) Bool) ;  sort function

(declare-fun len_eq ( (List AB) (List AB) ) Bool) ; check list length equality

(assert
  (split nil (pair nil nil))
)

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
  (forall ((X AB))
    (split (insert X nil) (pair nil (insert X nil)))
  )
)

(assert
  (forall ((X AB) (Y AB) (L (List AB)) (L1 (List AB)) (L2 (List AB)))
    (=>
      (split L (pair L1 L2))
      (split (insert X (insert Y L)) (pair (insert X L1) (insert Y L2)))
    )
  )
)

(assert
  (forall ((L (List AB)))
    (merge (pair nil L) L)
  )
)

(assert
  (forall ((L (List AB)))
    (merge (pair L nil) L)
  )
)

(assert
  (forall ((L (List AB)) (L1 (List AB)) (L2 (List AB)))
    (=>
      (merge (pair L1 L2) L)
      (merge (pair (insert a L1) L2) (insert a L))
    )
  )
)

(assert
  (forall ((L (List AB)) (L1 (List AB)) (L2 (List AB)))
    (=>
      (merge (pair (insert b L1) L2) L)
      (merge (pair (insert b L1) (insert a L2)) (insert a L))
    )
  )
)

(assert
  (forall ((L (List AB)) (L1 (List AB)) (L2 (List AB)))
    (=>
      (merge (pair L1 L2) L)
      (merge (pair (insert b L1) (insert b L2)) (insert b (insert b L)))
    )
  )
)

(assert
  (sort nil nil)
)

(assert
  (forall ((X AB))
    (sort (insert X nil) (insert X nil))
  )
)

(assert
  (forall ((X AB) (Y AB) (L (List AB)) (L1 (List AB)) (L2 (List AB)) (M1 (List AB)) (M2 (List AB)) (M (List AB)))
    (=>
      (and
        (split (insert X (insert Y L)) (pair L1 L2))
        (sort L1 M1)
        (sort L2 M2)
        (merge (pair M1 M2) M)
      )
      (sort (insert X (insert Y L)) M)
    )
  )
)

(assert
  (forall ((L (List AB)) (S (List AB)))
    (not
      (and
        (sort L S)
        (not (sorted S))
      )
    )
  )
)

(check-sat)
(get-model)
