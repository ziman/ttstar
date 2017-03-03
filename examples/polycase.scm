(print
  (letrec* (
    (Q (list 'Q))
    (W (list 'W))
    (T (list 'T))
    (F (list 'F))
    (not_TT (error "NOT IMPLEMENTED"))
    (mot (error "NOT IMPLEMENTED"))
    (invert (error "NOT IMPLEMENTED"))
    (main ((invert F) Q))
  )
    main))
