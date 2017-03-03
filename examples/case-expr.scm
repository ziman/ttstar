(print
  (letrec* (
    (T (list 'T))
    (F (list 'F))
    (MkUnit (list 'MkUnit))
    (not_TT (error "NOT IMPLEMENTED"))
    (main (not_TT (letrec* ((f (error "NOT IMPLEMENTED")))
      (f (not_TT F)))))
  )
    main))
