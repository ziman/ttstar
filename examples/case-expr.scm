(require-extension matchable)
(print
  (letrec* (
    (T `(T))
    (F `(F))
    (MkUnit `(MkUnit))
    (not_TT (lambda (_e0)
      (match (list _e0)
        [(('T))
          F]
        [(('F))
          T])))
    (main (not_TT (letrec* ((f (lambda (_e0)
      (match (list _e0)
        [(('F))
          MkUnit]
        [(('T))
          F]))))
      (f (not_TT F)))))
  )
    main))
