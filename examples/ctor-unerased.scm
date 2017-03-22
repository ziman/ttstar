(require-extension matchable)
(define Type '(Type))
(print
  (letrec* (
    (Bool `(Bool))
    (T `(T))
    (F `(F))
    (Unit `(Unit))
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
