(require-extension matchable)
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
    (f (lambda (_e0)
      (match (list _e0)
        [(('T))
          id]
        [(('F))
          constT])))
    (main ((TB ((f T) F)) (f F)))
  )
    main))
