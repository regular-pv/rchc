(set-logic HORN)
; over-approximate the insert-sort function
; and check that it preserves the length of the list.

(declare-fun leq ( AB AB ) Bool) ; exact

(assert (leq a a))
(assert (leq a b))
(assert (not (leq b a)))
(assert (leq b b))

; (declare-fun sorted ( (List AB) ) Bool) ; exact
;
; (assert
; 	(sorted nil)
; )
; (assert
; 	(forall ((x AB)) (sorted (insert x nil)))
; )
; (assert
; 	(forall ( (x AB) (y AB) (l (List AB)) ) (<=> (and (leq x y) (sorted (insert y l))) (sorted (insert x (insert y l)))) )
; )

(declare-fun sort_insert ( AB (List AB) (List AB) ) Bool) ; over-approx

(assert
	(forall ((x AB)) (sort_insert x nil (insert x nil)))
)
(assert
	(forall ((x AB) (y AB) (l (List AB))) (=> (leq x y) (sort_insert x (insert y l) (insert x (insert y l)))))
)
(assert
	(forall ((x AB) (y AB) (l (List AB)) (l2 (List AB))) (=> (and (not (leq x y)) (sort_insert x l l2)) (sort_insert x (insert y l) (insert y l2))))
)

(declare-fun sort ((List AB) (List AB)) Bool) ; over-approx

(assert
	(sort nil nil)
)
(assert
	(forall ((x AB) (l (List AB)) (l2 (List AB)) (l3 (List AB))) (=> (and (sort l l2) (sort_insert x l2 l3)) (sort (insert x l) l3)))
)

(declare-fun len_eq ( (List AB) (List AB) ) Bool) ; exact

(assert
	(len_eq nil nil)
)
(assert
	(forall ((x AB) (y AB) (l1 (List AB)) (l2 (List AB))) (<=> (len_eq l1 l2) (len_eq (insert x l1) (insert y l2))))
)

;; properties to verify

; sort sorts.
; (assert
; 	(forall ((l (List AB)) (l2 (List AB))) (=> (sort l l2) (sorted l2)))
; )

; sort preserves len
(assert
	(forall ((l (List AB)) (l2 (List AB))) (=> (sort l l2) (len_eq l l2)))
)

(check-sat)
(get-model)
