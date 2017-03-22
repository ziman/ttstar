(require-extension matchable)
(define Type '(Type))
(print
  (letrec* (
    (T `(T))
    (F `(F))
    (MkUnit `(MkUnit))
    (not_TT (lambda (_e0)
      (match (list _e0)
        [(('T))
          MkUnit]
        [(('F))
          MkUnit])))
    (main (not_TT T))
  )
    main))
