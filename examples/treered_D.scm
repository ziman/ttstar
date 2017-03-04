(require-extension matchable)
(print
  (letrec* (
    (True (list 'True))
    (False (list 'False))
    (Yeah (list 'Yeah))
    (Nope (list 'Nope))
    (Nothing (list 'Nothing))
    (Just (lambda (x)
      (list 'Just x)))
    (g (lambda (_e0)
      (match (list _e0)
        [(('Just ('True)))
          Yeah]
        [(('Just ('False)))
          Nope]
        [(('Nothing))
          Nope])))
    (main (g (Just True)))
  )
    main))
