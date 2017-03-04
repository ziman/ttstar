(require-extension matchable)
(print
  (letrec* (
    (T (list 'T))
    (F (list 'F))
    (not_TT (lambda (_e0)
      (match (list _e0)
        [(('T))
          F]
        [(('F))
          T])))
    (main not_TT)
  )
    main))
