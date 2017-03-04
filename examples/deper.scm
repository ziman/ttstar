(print
  (letrec* (
    (T (list 'T))
    (F (list 'F))
    (TB (lambda (x)
      (lambda (y)
        (list 'TB x y))))
    (id (lambda (x)
      x))
    (constT T)
    (f (error "NOT IMPLEMENTED"))
    (main ((TB ((f T) F)) (f F)))
  )
    main))
