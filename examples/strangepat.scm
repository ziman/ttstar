(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (T `(T))
    (P (lambda (_x0)
      `(P ,_x0)))
    (fst (lambda (_e0)
      (match (list _e0)
        [(('P y))
          y])))
    (main (fst (P T)))
  )
    main))
