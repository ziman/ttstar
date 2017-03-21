(require-extension matchable)
(print
  (letrec* (
    (T `(T))
    (P (lambda (_x0)
      `(P ,_x0)))
    (fst (lambda (_e0)
      (match (list _e0)
        [(('P y))
          y])))
    (main (fst (P T)))
  )
    main))
