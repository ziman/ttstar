(print
  (letrec (
    (T (list 'T))
    (P (lambda (e0)
      (list 'P e0)))
    (fst (lambda (x)
      (case (car x)
        ((P) (let* (
          (_args-y (cdr x))
          (y (car _args-y))
        )
          y)))))
    (main (fst (P T)))
  )
    main))
(newline)
