(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (Bool `(Bool))
    (T `(T))
    (F `(F))
    (Pair `(Pair))
    (P (lambda (_x0)
      (lambda (_x1)
        `(P ,_x0 ,_x1))))
    (fst (lambda (_e0)
      (match (list _e0)
        ((('P y))
          y))))
    (main (fst (P T)))
  )
    main))
