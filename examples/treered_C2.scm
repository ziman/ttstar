(print
  (letrec* (
    (Z (list 'Z))
    (vlen (lambda (n)
      n))
    (main (vlen Z))
  )
    main))
