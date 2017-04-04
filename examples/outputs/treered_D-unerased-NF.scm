(require-extension matchable)
(define Type #(Type))
(define (number->peano z s i) (if (= i 0) (vector z) (vector s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (Bool (vector 'Bool))
    (True (vector 'True))
    (Foo (lambda (_x0)
      (vector 'Foo _x0)))
    (Yeah (vector 'Yeah))
  )
    Yeah))
