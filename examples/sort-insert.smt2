(set-logic HORN)

(declare-datatypes ( (List 1) )
  (
    (par (T) ( (nil) (insert (head T) (tail (List T))) ))
  )
)

(declare-datatypes ( (AB 0) )
  (
    ( (a) (b) )
  )
)

(declare-fun all_b ( (List AB) ) Bool) ; needed to define `sorted`
(declare-fun sorted ( (List AB) ) Bool) ; sorted lists

(declare-fun sort_insert ( AB (List AB) (List AB) ) Bool) ; insert function
(declare-fun sort ( (List AB) (List AB) ) Bool) ;  sort function

(declare-fun len_eq ( (List AB) (List AB) ) Bool) ; check list length equality

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
  (forall ((X AB)) (sort_insert X nil (insert X nil)))
)

(assert
  (forall ((X AB) (L (List AB))) (sort_insert X (insert b L) (insert X (insert b L))))
)

(assert
  (forall ((L (List AB))) (sort_insert a (insert a L) (insert a (insert a L))))
)

(assert
  (forall ((L (List AB)) (M (List AB)))
    (=>
      (sort_insert b L M)
      (sort_insert b (insert a L) (insert a M))
    )
  )
)

(assert
  (sort nil nil)
)

(assert
  (forall ((X AB) (L (List AB)) (M (List AB)) (S (List AB)))
    (=>
      (and
        (sort L M)
        (sort_insert X M S)
      )
      (sort (insert X L) S)
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

(assert
  (len_eq nil nil)
)

(assert
  (forall ((X AB) (Y AB) (L (List AB)) (M (List AB)))
    (=>
      (len_eq L M)
      (len_eq (insert X L) (insert Y M))
    )
  )
)

(assert
  (forall ((X AB) (L (List AB)))
    (not (len_eq nil (insert X L)))
  )
)

(assert
  (forall ((X AB) (L (List AB)))
    (not (len_eq (insert X L) nil))
  )
)

(assert
  (forall ((X AB) (Y AB) (L (List AB)) (M (List AB)))
    (=>
      (not (len_eq L M))
      (not (len_eq (insert X L) (insert Y M)))
    )
  )
)

(assert
  (forall ((X AB) (L (List AB)) (M (List AB)) (S (List AB)))
    (=>
      (sort L M)
      (len_eq L M)
    )
  )
)

(check-sat)
(get-model)
