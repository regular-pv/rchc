; length(make_list(n)) = n
;
; NOTE: we use the `Tsil` type instead of `List` so that the
;       standard convolution can be used.
(set-logic HORN)

; make_list function
(declare-fun rev ( (List Nat) ) Bool)

(check-sat)
(get-model)
