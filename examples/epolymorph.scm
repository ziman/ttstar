(require-extension matchable)
(print
  (letrec* (
    (Z (list 'Z))
    (S (lambda (n)
      (list 'S n)))
    (Plus (lambda (x)
      (lambda (y)
        (list 'Plus x y))))
    (id (lambda (_e0)
      (match (list _e0)
        [(('Z))
          Z]
        [(('S y))
          (letrec* ((result (S y)))
            result)])))
    (const_3 (lambda (x)
      (S (S (S Z)))))
    (two (S (S Z)))
    (f (lambda (g)
      (lambda (z)
        (lambda (h)
          (lambda (w)
            ((Plus (g z)) (h w)))))))
    (apply_TT (lambda (f)
      (lambda (x)
        (f x))))
    (test_1 ((Plus ((apply_TT id) (S (S Z)))) ((apply_TT const_3) two)))
    (test_2 ((((f id) (S (S Z))) const_3) (S Z)))
    (main ((Plus test_1) test_2))
  )
    main))
