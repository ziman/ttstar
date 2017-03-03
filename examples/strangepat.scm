(print
  (letrec* (
    (T (list 'T))
    (P (lambda (_x0)
      (list 'P _x0)))
    (fst (error "NOT IMPLEMENTED"))
    (main (fst (P T)))
  )
    main))
