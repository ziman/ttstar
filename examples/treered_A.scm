(print
  (letrec* (
    (Z (list 'Z))
    (S (lambda (x)
      (list 'S x)))
    (Nil (list 'Nil))
    (Cons (lambda (x)
      (lambda (xs)
        (list 'Cons x xs))))
    (vlen (error "NOT IMPLEMENTED"))
    (main (vlen ((Cons (S (S (S Z)))) Nil)))
  )
    main))
