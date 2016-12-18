(print
  (letrec* (
    (F (list 'F))
    (Refl (list 'Refl))
    (notnot (lambda (x)
      (case (car x)
        ((F) Refl))))
    (main (notnot F))
  )
    main))
(newline)
