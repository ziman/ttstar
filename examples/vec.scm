(require-extension matchable)
(define Type '(Type))
(print
  (letrec* (
    (Z `(Z))
    (S (lambda (x)
      `(S ,x)))
    (Nil `(Nil))
    (Cons (lambda (x)
      (lambda (xs)
        `(Cons ,x ,xs))))
    (append_TT (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          [(('Nil) ys)
            ys]
          [(('Cons x xs) ys)
            ((Cons x) ((append_TT xs) ys))]))))
    (main ((append_TT Nil) ((Cons (S (S (S (S Z))))) Nil)))
  )
    main))
