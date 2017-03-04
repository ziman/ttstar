(require-extension matchable)
(print
  (letrec* (
    (T (list 'T))
    (F (list 'F))
    (MkUnit (list 'MkUnit))
    (not_TT (lambda (_e0)
      (match (list _e0)
        [(('T))
          MkUnit]
        [(('F))
          MkUnit])))
    (main (not_TT T))
  )
    main))
