(require-extension matchable)
(print
  (letrec* (
    (Z `(Z))
    (S (lambda (x)
      `(S ,x)))
    (Nil `(Nil))
    (Cons (lambda (x)
      (lambda (xs)
        `(Cons ,x ,xs))))
    (vlen (lambda (_e0)
      (match (list _e0)
        [(('Nil))
          Z]
        [(('Cons _ ys))
          (S (vlen ys))])))
    (main (vlen ((Cons (S (S (S Z)))) Nil)))
  )
    main))
