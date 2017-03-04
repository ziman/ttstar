(require-extension matchable)
(print
  (letrec* (
    (T (list 'T))
    (F (list 'F))
    (MkUnit (list 'MkUnit))
    (not_TT (match-lambda*
      [(('T))
        MkUnit]
      [(('F))
        MkUnit]))
    (main (not_TT T))
  )
    main))
