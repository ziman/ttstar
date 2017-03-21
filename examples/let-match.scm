(require-extension matchable)
(print
  (letrec* (
    (T `(T))
    (F `(F))
    (main ((letrec* ((not_TT (lambda (_e0)
      (match (list _e0)
        [(('T))
          F]
        [(('F))
          T]))))
      not_TT) F))
  )
    main))
