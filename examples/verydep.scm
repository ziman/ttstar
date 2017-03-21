(require-extension matchable)
(print
  (letrec* (
    (Just (lambda (x)
      `(Just ,x)))
    (Nothing `(Nothing))
    (Bool `(Bool))
    (False `(False))
    (f (lambda (_e0)
      (match (list _e0)
        [(('Just b))
          b]
        [(('Nothing))
          Bool])))
    (main (f (Just False)))
  )
    main))
