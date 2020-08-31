(set-logic HORN)

(declare-fun + ( Nat Nat Nat ) Bool)

(assert (forall ((y Nat)) (+ 0 y y)))
; (assert (forall ((x Nat)) (+ x 0 x)))
(assert (forall ((x Nat) (y Nat) (z Nat)) (=> (+ x y z) (+ (s x) y (s z)))))
; (assert (forall ((x Nat) (y Nat) (z Nat)) (=> (+ x y z) (+ x (s y) (s z)))))

; function
(assert (forall ((x Nat) (y Nat) (z Nat) (w Nat)) (=> (and (+ x y z) (+ x y w)) (= z w))))

(check-sat)
(get-model)
