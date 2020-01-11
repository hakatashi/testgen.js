(set-logic ALL)
(set-option :produce-models true)

(define-sort FP () (_ FloatingPoint 11 53))
(define-fun toFP ((n Real)) FP ((_ to_fp 11 53) RNE n))

(declare-const x FP)
(declare-const y FP)

(assert
  (and
    (fp.gt x (toFP 0))
    (fp.eq (fp.roundToIntegral RNE x) x)
    (fp.leq x (toFP 3))
    (fp.gt y (toFP 0))
    (fp.eq (fp.roundToIntegral RNE y) y)
    (fp.leq y (toFP 3))
    (not (fp.eq x y))
    (not
      (let ((z (fp.sub RNE (toFP 6) (fp.add RNE x y))))
        (and
          (not (fp.eq z x))
          (not (fp.eq z y)))))))

(check-sat)
(get-model)
