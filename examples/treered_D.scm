(print
  (letrec (
    (True (list 'True))
    (Yeah (list 'Yeah))
    (Nope (list 'Nope))
    (Just (lambda (x)
      (list 'Just x)))
    (g (lambda (x)
      (case (car x)
        ((Just) (let* (
          (_args-b (cdr x))
          (b (car _args-b))
        )
          (case (car b)
            ((True) Yeah)))))))
    (main (g (Just True)))
  )
    main))
(newline)
