(print
  (letrec* (
    (Z (list 'Z))
    (S (lambda (_x0)
      (list 'S _x0)))
    (plus (error "NOT IMPLEMENTED"))
    (main (letrec* ((pred (error "NOT IMPLEMENTED")))
      ((plus (pred (S (S (S (S Z)))))) (pred (S (S (S (S (S Z)))))))))
  )
    main))
