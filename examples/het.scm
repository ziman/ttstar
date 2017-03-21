(require-extension matchable)
(print
  (letrec* (
    (Tuple (lambda (x)
      (lambda (y)
        (lambda (z)
          (lambda (w)
            `(Tuple ,x ,y ,z ,w))))))
    (Bool `(Bool))
    (T `(T))
    (F `(F))
    (Mool `(Mool))
    (Q `(Q))
    (W `(W))
    (f (lambda (_e0)
      (match (list _e0)
        [(('T))
          Bool]
        [(('F))
          Mool]
        [(('Q))
          Bool]
        [(('W))
          Mool])))
    (main ((((Tuple (f T)) (f F)) (f Q)) (f W)))
  )
    main))
