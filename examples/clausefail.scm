(require-extension matchable)
(print
  (letrec* (
    (S (list 'S))
    (T (list 'T))
    (F (list 'F))
    (isSuc (lambda (_e0)
      (match (list _e0)
        [(('S))
          T]
        [(n)
          F])))
    (main (lambda (x)
      (isSuc x)))
  )
    main))
