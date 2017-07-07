(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (N `(N))
    (Z `(Z))
    (S (lambda (x)
      `(S ,x)))
    (Vec (lambda (_x0)
      (lambda (_x1)
        `(Vec ,_x0 ,_x1))))
    (Nil (lambda (a)
      `(Nil ,a)))
    (Cons (lambda (a)
      (lambda (n)
        (lambda (x)
          (lambda (xs)
            `(Cons ,a ,n ,x ,xs))))))
    (vlen (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          (((_) ('Nil _))
            Z)
          (((_ m) ('Cons _ _ y ys))
            (S ((vlen m) ys)))))))
    (main ((vlen (S Z)) ((((Cons N) Z) (S (S (S Z)))) (Nil N))))
  )
    main))
