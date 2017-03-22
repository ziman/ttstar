(require-extension matchable)
(define Type '(Type))
(print
  (letrec* (
    (subst (match (list)
      [()
        (lambda (w)
          w)]))
    (T `(T))
    (F `(F))
    (Nil `(Nil))
    (Cons (lambda (x)
      (lambda (xs)
        `(Cons ,x ,xs))))
    (RNil `(RNil))
    (RSnoc (lambda (x)
      (lambda (rxs)
        `(RSnoc ,x ,rxs))))
    (rev_ (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          [(rxs ('Nil))
            (subst rxs)]
          [(rxs ('Cons y ys))
            (subst ((rev_ ((RSnoc y) rxs)) ys))]))))
    (rev (lambda (xs)
      ((rev_ RNil) xs)))
    (reverse_ (lambda (_e0)
      (match (list _e0)
        [(('RNil))
          Nil]
        [(('RSnoc x rxs))
          ((Cons x) (reverse_ rxs))])))
    (reverse_TT (lambda (xs)
      (reverse_ (rev xs))))
    (main (reverse_TT ((Cons T) ((Cons F) ((Cons T) ((Cons F) Nil))))))
  )
    main))
