(require-extension matchable)
(define Type '(Type))
(print
  (letrec* (
    (A `(A))
    (B `(B))
    (Op (lambda (x)
      (lambda (y)
        `(Op ,x ,y))))
    (id (lambda (x)
      x))
    (const_A A)
    (f (lambda (g)
      (lambda (z)
        (lambda (h)
          ((Op (g z)) h)))))
    (main (((f id) B) const_A))
  )
    main))
