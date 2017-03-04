(require-extension matchable)
(print
  (letrec* (
    (Tuple (lambda (x)
      (lambda (y)
        (lambda (z)
          (lambda (w)
            (list 'Tuple x y z w))))))
    (Bool (list 'Bool))
    (T (list 'T))
    (F (list 'F))
    (Mool (list 'Mool))
    (Q (list 'Q))
    (W (list 'W))
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
