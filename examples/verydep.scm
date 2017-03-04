(require-extension matchable)
(print
  (letrec* (
    (Just (lambda (x)
      (list 'Just x)))
    (Nothing (list 'Nothing))
    (Bool (list 'Bool))
    (False (list 'False))
    (f (lambda (_e0)
      (match (list _e0)
        [(('Just b))
          b]
        [(('Nothing))
          Bool])))
    (main (f (Just False)))
  )
    main))
