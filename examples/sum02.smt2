; property: x + 0 = 0 + x
(set-logic HORN)

(declare-fun + ( Nat Nat Nat ) Bool) ; over-approx
(assert (forall ((y Nat)) (+ 0 y y)))
(assert (forall ((x Nat) (y Nat) (z Nat)) (<= (+ (s x) y (s z)) (+ x y z))))

; actual property
;(assert (forall ((x Nat) (y Nat)) (not (+ x (s y) x))))
(assert
	(forall ((x Nat) (a Nat) (b Nat))
		(=>
			(and (+ 0 x a) (+ x 0 b))
			(= a b)
		)
	)
)

(check-sat)
(get-model)
