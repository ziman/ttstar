(require-extension matchable)
(print
  (letrec* (
    (Z (list 'Z))
    (S (lambda (n)
      (list 'S n)))
    (VNil (list 'VNil))
    (VCons (lambda (xs)
      (list 'VCons xs)))
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
