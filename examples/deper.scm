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
    (f (lambda (x)
      (case (car x)
        ((T) id)
        ((F) constT))))
    (main ((TB ((f T) F)) (f F)))
  )
    main))
