(print
  (letrec* (
    (T (list 'T))
    (broken (error "NOT IMPLEMENTED"))
    (eek (error "NOT IMPLEMENTED"))
    (main (eek (broken T)))
  )
    main))
