(require-extension matchable)
(print
  (letrec* (
    (Z (list 'Z))
    (S (list 'S))
    (plus (match-lambda*
      [(('Z) m)
        m]
      [(('S) m)
        S]))
    (main ((plus S) S))
  )
    main))
