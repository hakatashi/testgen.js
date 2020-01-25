(set-logic ALL)
(set-option :produce-models true)

(define-sort FP () (_ FloatingPoint 11 53))
(define-fun toFP ((n Real)) FP ((_ to_fp 11 53) RNE n))

(declare-const x FP)
(declare-const y FP)

(assert
  (and
    (fp.gt x (toFP 0))
    (fp.leq x (toFP 3))
    (fp.eq (fp.roundToIntegral RNE x) x)
    (fp.gt y (toFP 0))
    (fp.leq y (toFP 3))
    (fp.eq (fp.roundToIntegral RNE y) y)
    (not (fp.eq x y))
    (not
      (let ((ans (fp.sub RNE (toFP 6) (fp.add RNE x y))))
        (and
          (fp.gt ans (toFP 0))
          (fp.leq ans (toFP 3))
          (fp.eq (fp.roundToIntegral RNE ans) ans)
          (not (fp.eq ans x))
          (not (fp.eq ans y)))))))

(check-sat)
(get-model)
