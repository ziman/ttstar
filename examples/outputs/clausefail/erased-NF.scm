(import (chicken process-context))
(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (S `(S))
    (T `(T))
    (F `(F))
    (isSuc (lambda (_e0)
      (match (list _e0)
        ((('S))
          T)
        ((n)
          F))))
  )
    (lambda (x)
      (isSuc x))))
