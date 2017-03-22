(require-extension matchable)
(define Type '(Type))
(print
  (letrec* (
    (Bool `(Bool))
    (T `(T))
    (F `(F))
    (not_TT (lambda (_e0)
      (match (list _e0)
        [(('T))
          F]
        [(('F))
          T])))
    (main not_TT)
  )
    main))
