(print
  (letrec* (
    (Z (list 'Z))
    (S (lambda (x)
      (list 'S x)))
    (Nil (list 'Nil))
    (Cons (lambda (n)
      (lambda (xs)
        (list 'Cons n xs))))
    (vlen (lambda (n)
      (lambda (xs)
        (case (car xs)
          ((Nil) n)
          ((Cons) (let* (
            (_args-m (cdr xs))
            (m (car _args-m))
          )
            (let* (
              (_args-ys (cdr _args-m))
              (ys (car _args-ys))
            )
              (S ((vlen m) ys)))))))))
    (main ((vlen (S Z)) ((Cons Z) Nil)))
  )
    main))
(newline)
