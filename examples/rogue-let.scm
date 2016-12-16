(print
  (letrec (
    (T (list 'T))
    (F (list 'F))
    (not_TT (lambda (x)
      (case (car x)
        ((T) F)
        ((F) T))))
    (main not_TT)
  )
    main))
(newline)
