(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (T `(T))
    (F `(F))
    (MkUnit `(MkUnit))
    (not_TT (lambda (_e0)
      (match (list _e0)
        [(('T))
          F]
        [(('F))
          T])))
    (main (not_TT (letrec* ((f (lambda (_e0)
      (match (list _e0)
        [(('F))
          MkUnit]
        [(('T))
          F]))))
      (f (not_TT F)))))
  )
    main))
