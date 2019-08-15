(set-logic ALL)
(set-option :produce-models true)

(define-sort FP () (_ FloatingPoint 11 53))

(define-fun one () FP (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000))
(define-fun maxSafeInteger () FP (fp #b0 #b10000110011 #b1111111111111111111111111111111111111111111111111111))

(declare-const x FP)

(assert (fp.isPositive x))
(assert (fp.leq x maxSafeInteger))
(assert (fp.eq (fp.roundToIntegral RNE x) x))
(assert (distinct (fp.sub RNE (fp.add RNE one x) x) one))

(check-sat)
(get-model)
