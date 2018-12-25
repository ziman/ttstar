(import (chicken process-context))
(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (True `(True))
    (False `(False))
    (Z `(Z))
    (S (lambda (_x0)
      `(S ,_x0)))
    (Even `(Even))
    (Odd `(Odd))
    (fun (lambda (_e0)
      (match (list _e0)
        ((('Even))
          (lambda (n)
            (letrec* ((f (lambda (_e0)
              (match (list _e0)
                ((('Z))
                  True)
                ((('S m))
                  ((fun Odd) m))))))
              (f n))))
        ((('Odd))
          (lambda (n)
            (letrec* ((f (lambda (_e0)
              (match (list _e0)
                ((('Z))
                  False)
                ((('S m))
                  ((fun Even) m))))))
              (f n)))))))
    (even (fun Even))
    (main (even (S (S (S (S (S (S (S (S Z))))))))))
  )
    main))
