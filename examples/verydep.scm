(print
  (letrec* (
    (Just (lambda (x)
      (list 'Just x)))
    (Bool (list 'Bool))
    (False (list 'False))
    (f (lambda (x)
      (case (car x)
        ((Just) (let* (
          (_args-b (cdr x))
          (b (car _args-b))
        )
          b)))))
    (main (f (Just False)))
  )
    main))
(newline)
