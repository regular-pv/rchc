(declare-datatypes ( (Nat 0) )
  (
    ( (0) (s (predecessor Nat)) )
  )
)

(declare-datatypes ( (List 1) )
  (
    (par (T) ( (nil) (insert (head T) (tail (List T))) ))
  )
)

(declare-datatypes ( (Tsil 1) )
  (
    (par (T) ( (lin) (tresni (liat (Tsil T)) (daeh T)) ))
  )
)
