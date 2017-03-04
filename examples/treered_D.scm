(print
  (letrec* (
    (True (list 'True))
    (False (list 'False))
    (Yeah (list 'Yeah))
    (Nope (list 'Nope))
    (Nothing (list 'Nothing))
    (Just (lambda (x)
      (list 'Just x)))
    (g (error "NOT IMPLEMENTED"))
    (main (g (Just True)))
  )
    main))
