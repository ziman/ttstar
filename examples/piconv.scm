(require-extension matchable)
(define Type '(Type))
(print
  (letrec* (
    (A `(A))
    (const_A A)
    (apply_TT (lambda (f)
      f))
    (main (apply_TT const_A))
  )
    main))
