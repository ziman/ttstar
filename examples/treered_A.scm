(require-extension matchable)
(print
  (letrec* (
    (Z (list 'Z))
    (S (lambda (x)
      (list 'S x)))
    (Nil (list 'Nil))
    (Cons (lambda (x)
      (lambda (xs)
        (list 'Cons x xs))))
    (vlen (lambda (_e0)
      (match (list _e0)
        [(('Nil))
          Z]
        [(('Cons y ys))
          (S (vlen ys))])))
    (main (vlen ((Cons (S (S (S Z)))) Nil)))
  )
    main))
