(require-extension matchable)
(define Type '(Type))
(print
  (letrec* (
    (T `(T))
    (A `(A))
    (B `(B))
    (Op (lambda (x)
      (lambda (y)
        `(Op ,x ,y))))
    (id (lambda (y)
      y))
    (constA (lambda (x)
      A))
    (apply_TT (lambda (f)
      (lambda (x)
        (f x))))
    (apply_REE (lambda (f)
      (lambda (x)
        (f x))))
    (apply_RRR (lambda (f)
      (lambda (x)
        (f x))))
    (test1 ((apply_RRR id) B))
    (test2 ((apply_REE constA) B))
    (main ((Op test1) test2))
  )
    main))
