(print
  (letrec* (
    (True (list 'True))
    (False (list 'False))
    (Z (list 'Z))
    (S (lambda (_x0)
      (list 'S _x0)))
    (Even (list 'Even))
    (Odd (list 'Odd))
    (fun (error "NOT IMPLEMENTED"))
    (even (fun Even))
    (main (even (S (S (S (S (S (S (S (S Z))))))))))
  )
    main))
