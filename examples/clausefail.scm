(require-extension matchable)
(print
  (letrec* (
    (S `(S))
    (T `(T))
    (F `(F))
    (isSuc (lambda (_e0)
      (match (list _e0)
        [(('S))
          T]
        [(_)
          F])))
    (main (lambda (x)
      (isSuc x)))
  )
    main))
