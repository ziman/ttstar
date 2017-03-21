(require-extension matchable)
(print
  (letrec* (
    (Q `(Q))
    (W `(W))
    (T `(T))
    (F `(F))
    (not_TT (lambda (_e0)
      (match (list _e0)
        [(('T))
          F]
        [(('F))
          T])))
    (mot (lambda (_e0)
      (match (list _e0)
        [(('Q))
          W]
        [(('W))
          Q])))
    (invert (lambda (_e0)
      (match (list _e0)
        [(('T))
          not_TT]
        [(('F))
          mot])))
    (main ((invert F) Q))
  )
    main))
