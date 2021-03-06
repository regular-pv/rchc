(set-logic HORN)

(declare-fun leq ( Nat Nat ) Bool) ;

(assert
	(forall ( (n Nat) ) (leq 0 n) )
)
(assert
	(forall ( (n Nat) ) (not (leq (s n) 0)) )
)
(assert
	(forall ( (n Nat) (m Nat) ) (<=> (leq n m) (leq (s n) (s m)) ) )
)

(check-sat)
