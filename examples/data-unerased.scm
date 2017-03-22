(require-extension matchable)
(define Type '(Type))
(print
  (letrec* (
    (N `(N))
    (Z `(Z))
    (S (lambda (_x0)
      `(S ,_x0)))
    (plus (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          [(('Z) m)
            m]
          [(('S n) m)
            (S ((plus n) m))]))))
    (main (letrec* ((pred (lambda (_e0)
      (match (list _e0)
        [(('Z))
          Z]
        [(('S n))
          n]))))
      ((plus (S (S Z))) (S (S (S Z))))))
  )
    main))
