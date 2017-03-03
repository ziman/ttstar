(print
  (letrec* (
    (T (list 'T))
    (F (list 'F))
    (not_TT (error "NOT IMPLEMENTED"))
    (main not_TT)
  )
    main))
