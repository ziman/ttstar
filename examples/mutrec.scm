(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (T `(T))
    (F `(F))
    (g (lambda (_e0)
      (match (list _e0)
        ((('T))
          (letrec* ((h (lambda (_e0)
            (match (list _e0)
              ((('F))
                (g F))
              ((('T))
                T)))))
            (h F)))
        ((('F))
          T))))
    (main (g T))
  )
    main))
