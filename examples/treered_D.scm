(require-extension matchable)
(print
  (letrec* (
    (True `(True))
    (False `(False))
    (Yeah `(Yeah))
    (Nope `(Nope))
    (Nothing `(Nothing))
    (Just (lambda (x)
      `(Just ,x)))
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
