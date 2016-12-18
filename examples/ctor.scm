(print
  (letrec* (
    (T (list 'T))
    (MkUnit (list 'MkUnit))
    (not_TT (lambda (x)
      (case (car x)
        ((T) MkUnit))))
    (main (not_TT T))
  )
    main))
