(require-extension matchable)
(print
  (letrec* (
    (T `(T))
    (F `(F))
    (Refl `(Refl))
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
