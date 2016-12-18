(print
  (letrec* (
    (T (list 'T))
    (F (list 'F))
    (main ((letrec* ((not_TT (lambda (x)
      (case (car x)
        ((T) F)
        ((F) T)))))
      not_TT) F))
  )
    main))
(newline)
