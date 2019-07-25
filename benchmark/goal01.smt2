(declare-datatypes ( (Int 0) (List 1) )
  (
   	( (zero) (s (succ Int)) )
    (par (T) ( (nil) (cons (value T) (tail (List T))) ))
  )
)

(declare-fun drop (Int (List Int) (List Int)) Bool)
(declare-fun take (Int (List Int) (List Int)) Bool)
(declare-fun append ((List Int) (List Int) (List Int)) Bool)
(declare-fun diff_list ((List Int) (List Int)) Bool)

(assert (forall ( (A (List Int)) (B (List Int)) )
  (=>
    (= A (as nil (List Int)))
    (append A B B)
  )
))


