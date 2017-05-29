(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (A `(A))
    (B `(B))
    (Op (lambda (x)
      (lambda (y)
        `(Op ,x ,y))))
    (constA A)
    (apply_RRR (lambda (f)
      (lambda (x)
        (f x))))
    (test1 ((apply_RRR (lambda (x)
      x)) B))
    (test2 constA)
    (main ((Op test1) test2))
  )
    main))
