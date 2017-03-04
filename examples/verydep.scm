(print
  (letrec* (
    (Just (lambda (x)
      (list 'Just x)))
    (Nothing (list 'Nothing))
    (Bool (list 'Bool))
    (False (list 'False))
    (f (error "NOT IMPLEMENTED"))
    (main (f (Just False)))
  )
    main))
