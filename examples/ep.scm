(require-extension matchable)
(print
  (letrec* (
    (A `(A))
    (B `(B))
    (Op (lambda (x)
      (lambda (y)
        `(Op ,x ,y))))
    (id (lambda (y)
      y))
    (constA A)
    (apply_REE (lambda (f)
      f))
    (apply_RRR (lambda (f)
      (lambda (x)
        (f x))))
    (test1 ((apply_RRR id) B))
    (test2 (apply_REE constA))
    (main ((Op test1) test2))
  )
    main))
