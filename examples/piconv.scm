(print
  (letrec* (
    (A (list 'A))
    (const_A A)
    (apply_TT (lambda (f)
      f))
    (main (apply_TT const_A))
  )
    main))
(newline)
