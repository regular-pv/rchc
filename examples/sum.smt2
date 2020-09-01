(set-logic HORN)

(declare-fun + ( Nat Nat Nat ) Bool)

(assert (forall ((y Nat)) (+ 0 y y)))
(assert (forall ((x Nat) (y Nat) (z Nat)) (=> (+ x y z) (+ (s x) y (s z)))))

; function (without this, rchc will find an overapproximation of +).
; (assert (forall ((x Nat) (y Nat) (z Nat) (w Nat)) (=> (and (+ x y z) (+ x y w)) (= z w))))

; (assert (forall ((x Nat)) (+ x 0 x)))
; (assert (forall ((x Nat) (y Nat)) (=> (+ x y x) (= y 0))))
(assert (forall ((x Nat) (y Nat)) (not (+ x (s y) x))))

(check-sat)
(get-model)
