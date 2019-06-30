(import (chicken process-context))
(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (N `(N))
    (O (lambda (b)
      `(O ,b)))
    (I (lambda (b)
      `(I ,b)))
    (add1 (lambda (_e0)
      (match (list _e0)
        ((('N))
          (I N))
        ((('O b))
          (I b))
        ((('I b))
          (O (add1 b))))))
    (main (match (list)
      (()
        (add1 (I N)))))
  )
    main))
