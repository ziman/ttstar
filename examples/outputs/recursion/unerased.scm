(import (chicken process-context))
(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (Bool `(Bool))
    (True `(True))
    (False `(False))
    (Nat `(Nat))
    (Z `(Z))
    (S (lambda (n)
      `(S ,n)))
    (Vec (lambda (_x0)
      (lambda (_x1)
        `(Vec ,_x0 ,_x1))))
    (VNil (lambda (a)
      `(VNil ,a)))
    (VCons (lambda (a)
      (lambda (n)
        (lambda (x)
          (lambda (xs)
            `(VCons ,a ,n ,x ,xs))))))
    (vlen (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((a _ ('VNil _))
              Z)
            ((a (_ n) ('VCons _ _ x xs))
              (S (((vlen a) n) xs))))))))
    (testVec ((((VCons Bool) (S Z)) True) ((((VCons Bool) Z) False) (VNil Bool))))
    (main (((vlen Bool) (S (S Z))) testVec))
  )
    main))
