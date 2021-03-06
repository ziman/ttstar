(import (chicken process-context))
(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (N `(N))
    (Z `(Z))
    (S (lambda (_x0)
      `(S ,_x0)))
    (Fin (lambda (_x1)
      `(Fin ,_x1)))
    (FZ (lambda (n)
      `(FZ ,n)))
    (FS (lambda (n)
      (lambda (x)
        `(FS ,n ,x))))
    (Pair `(Pair))
    (P (lambda (x)
      (lambda (y)
        `(P ,x ,y))))
  )
    ((P ((FS (S (S Z))) ((FS (S Z)) (FZ Z)))) ((FS (S (S (S Z)))) ((FS (S (S Z))) (FZ (S Z)))))))
