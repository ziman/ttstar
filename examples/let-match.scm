(print
  (letrec* (
    (T (list 'T))
    (F (list 'F))
    (main ((letrec* ((not_TT (error "NOT IMPLEMENTED")))
      not_TT) F))
  )
    main))
