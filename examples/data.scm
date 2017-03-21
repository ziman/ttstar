(require-extension matchable)
(print
  (letrec* (
    (Z `(Z))
    (S `(S))
    (plus (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          [(('Z) m)
            m]
          [(('S) _)
            S]))))
    (main ((plus S) S))
  )
    main))
