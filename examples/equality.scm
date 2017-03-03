(print
  (letrec* (
    (T (list 'T))
    (F (list 'F))
    (Refl (list 'Refl))
    (notnot (error "NOT IMPLEMENTED"))
    (subst (error "NOT IMPLEMENTED"))
    (main (notnot (subst F)))
  )
    main))
