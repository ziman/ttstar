(print
  (letrec (
    (True (list 'True))
    (False (list 'False))
    (Z (list 'Z))
    (S (lambda (x__0)
      (list 'S x__0)))
    (Even (list 'Even))
    (Odd (list 'Odd))
    (fun (lambda (tag)
      (case (car tag)
        ((Even) (lambda (n)
          (letrec ((casefun__0 (lambda (x__4)
            (case (car x__4)
              ((Z) True)
              ((S) (let* (
                (_args-n_ (cdr x__4))
                (n_ (car _args-n_))
              )
                ((fun Odd) n_)))))))
            (casefun__0 n))))
        ((Odd) (lambda (n)
          (letrec ((casefun__1 (lambda (x__5)
            (case (car x__5)
              ((Z) False)
              ((S) (let* (
                (_args-n_ (cdr x__5))
                (n_ (car _args-n_))
              )
                ((fun Even) n_)))))))
            (casefun__1 n)))))))
    (main ((fun Odd) (S (S (S (S (S Z)))))))
  )
    main))
(newline)
