(set-logic HORN)

(declare-fun + ( Nat Nat Nat ) Bool)

(assert (forall ((A Nat)) (+ A 0 A)))

(assert (forall ((A Nat)) (+ 0 A A)))

(assert (forall ((A Nat) (B Nat) (C Nat)) (=> (+ A B C) (+ (s A) B (s C)))))

(assert (forall ((A Nat) (B Nat) (C Nat)) (=> (+ A B C) (+ A (s B) (s C)))))

(assert (forall ((A Nat)) (not (+ 0 0 (s A)))))

(assert (forall ((A Nat) (B Nat) (C Nat)) (=> (not (+ A B C)) (not (+ (s A) B (s C))))))

(assert (forall ((A Nat) (B Nat) (C Nat)) (=> (not (+ A B C)) (not (+ A (s B) (s C))))))

(check-sat)
(get-model)
