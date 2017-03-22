(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (Z `(Z))
    (S `(S))
    (plus (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          [(('Z) m)
            m]
          [(('S) _)
            S]))))
    (main ((plus S) S))
  )
    main))
