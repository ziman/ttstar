(require-extension matchable)
(print
  (letrec* (
    (Z `(Z))
    (S (lambda (n)
      `(S ,n)))
    (VNil `(VNil))
    (VCons (lambda (xs)
      `(VCons ,xs)))
    (vlen (lambda (_e0)
      (match (list _e0)
        [(('VNil))
          Z]
        [(('VCons xs))
          (S (vlen xs))])))
    (testVec (VCons (VCons VNil)))
    (main (vlen testVec))
  )
    main))
