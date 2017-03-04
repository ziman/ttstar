(print
  (letrec* (
    (Z (list 'Z))
    (S (lambda (x)
      (list 'S x)))
    (Nil (list 'Nil))
    (Cons (lambda (x)
      (lambda (xs)
        (list 'Cons x xs))))
    (append_TT (error "NOT IMPLEMENTED"))
    (main ((append_TT Nil) ((Cons (S (S (S (S Z))))) Nil)))
  )
    main))
