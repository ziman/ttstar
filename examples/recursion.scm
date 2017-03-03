(print
  (letrec* (
    (Z (list 'Z))
    (S (lambda (n)
      (list 'S n)))
    (VNil (list 'VNil))
    (VCons (lambda (xs)
      (list 'VCons xs)))
    (vlen (error "NOT IMPLEMENTED"))
    (testVec (VCons (VCons VNil)))
    (main ((vlen (S (S Z))) testVec))
  )
    main))
