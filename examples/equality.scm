(require-extension matchable)
(print
  (letrec* (
    (T (list 'T))
    (F (list 'F))
    (Refl (list 'Refl))
    (notnot (lambda (_e0)
      (match (list _e0)
        [(('T))
          Refl]
        [(('F))
          Refl])))
    (subst (match (list)
      [()
        (lambda (w)
          w)]))
    (main (notnot (subst F)))
  )
    main))
