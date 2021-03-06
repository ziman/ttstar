(import (chicken process-context))
(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (Q `(Q))
    (W `(W))
    (T `(T))
    (F `(F))
    (not_TT (lambda (_e0)
      (match (list _e0)
        ((('T))
          F)
        ((('F))
          T))))
    (mot (lambda (_e0)
      (match (list _e0)
        ((('Q))
          W)
        ((('W))
          Q))))
    (invert (lambda (_e0)
      (match (list _e0)
        ((('T))
          not_TT)
        ((('F))
          mot))))
    (main ((invert F) Q))
  )
    main))
