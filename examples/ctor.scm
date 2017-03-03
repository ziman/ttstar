(print
  (letrec* (
    (T (list 'T))
    (F (list 'F))
    (MkUnit (list 'MkUnit))
    (not_TT (error "NOT IMPLEMENTED"))
    (main (not_TT T))
  )
    main))
