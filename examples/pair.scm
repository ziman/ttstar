(print
  (letrec* (
    (T (list 'T))
    (F (list 'F))
    (P (lambda (x)
      (lambda (y)
        (list 'P x y))))
    (fst (error "NOT IMPLEMENTED"))
    (snd (error "NOT IMPLEMENTED"))
    (and (error "NOT IMPLEMENTED"))
    (main ((and (fst ((P T) F))) (snd ((P F) T))))
  )
    main))
