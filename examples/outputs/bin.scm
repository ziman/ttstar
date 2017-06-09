(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (Z `(Z))
    (S (lambda (x)
      `(S ,x)))
    (True `(True))
    (False `(False))
    (N `(N))
    (C (lambda (rest)
      `(C ,rest)))
    (add_ (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((_ ('N) ('N))
              (C N))
            (((_ w) ('C xn) ('C yn))
              (letrec* ((f (match (list)
                (()
                  (C (((add_ w) xn) yn))))))
                f)))))))
    (add (lambda (w)
      (lambda (bx)
        (lambda (by)
          (((add_ w) bx) by)))))
    (inputSize (rts-arg-peano 'Z 'S 0))
    (mkBin (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((_ ('Z))
            N)
          ((('True) ('S n))
            (C ((mkBin False) n)))
          ((('False) ('S n))
            (C ((mkBin True) n)))))))
    (main (letrec* (
      (x ((mkBin True) inputSize))
      (y ((mkBin False) inputSize))
    )
      (((add inputSize) x) y)))
  )
    main))