(require-extension matchable)
(define Type '(Type))
(print
  (letrec* (
    (Z `(Z))
    (S (lambda (x)
      `(S ,x)))
    (plus (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          [(('Z) m)
            m]
          [(('S n) m)
            (S ((plus n) m))]))))
    (id (lambda (x)
      x))
    (const (lambda (x)
      (lambda (y)
        x)))
    (main (letrec* ((apply_TT (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          [(f ('Z))
            (f Z)]
          [(f ('S x))
            (f (S x))])))))
      (letrec* (
        (Q `(Q))
        (three (S (S (S Z))))
      )
        ((plus ((apply_TT id) (S (S Z)))) ((apply_TT (const Q)) three)))))
  )
    main))
