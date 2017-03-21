(require-extension matchable)
(print
  (letrec* (
    (P `(P))
    (f (lambda (_e0)
      (match (list _e0)
        [(c)
          c])))
    (main (f P))
  )
    main))
