(import (chicken process-context))
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
    (MkPair (lambda (_x7)
      (lambda (_x8)
        `(MkPair ,_x7 ,_x8))))
    (snd (lambda (_e0)
      (match (list _e0)
        (((_ x y))
          y))))
    (MkSt (lambda (run)
      `(MkSt ,run)))
    (runState (lambda (_e0)
      (match (list _e0)
        (((_ run))
          run))))
    (execState (lambda (x)
      (lambda (s)
        (snd ((runState x) s)))))
    (stGet (MkSt (lambda (s)
      ((MkPair s) s))))
    (stReturn (lambda (x)
      (MkSt (lambda (s)
        ((MkPair s) x)))))
    (stBind (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          (((_ f) g)
            (letrec* (
              (stBind3 (lambda (_e0)
                (lambda (_e1)
                  (match (list _e0 _e1)
                    ((s (_ f))
                      (f s))))))
              (stBind2 (lambda (_e0)
                (lambda (_e1)
                  (match (list _e0 _e1)
                    ((g (_ s x))
                      ((stBind3 s) (g x)))))))
            )
              (MkSt (lambda (s)
                ((stBind2 g) (f s))))))))))
    (ioReturn (lambda (x)
      (stReturn x)))
    (ioBind (lambda (x)
      (lambda (y)
        ((stBind x) y))))
    (ioWrapImpure (lambda (impureF)
      ((stBind stGet) (lambda (w)
        (stReturn (impureF w))))))
    (unsafePerformIO (lambda (x)
      (letrec* ((TheWorld `(TheWorld)))
        ((execState x) TheWorld))))
    (intS (lambda (x) (+ x 1)))
    (intZ 0)
    (printSchemeRepr (lambda (x)
      (letrec* ((nativePrint print))
        (ioWrapImpure (lambda (w)
          (nativePrint x))))))
    (natToInt (lambda (_e0)
      (match (list _e0)
        ((('Z))
          intZ)
        ((('S n))
          (intS (natToInt n))))))
    (intToNat (lambda (x) (number->peano 'Z 'S x)))
    (printNat (lambda (x)
      (printSchemeRepr (natToInt x))))
    (main (unsafePerformIO ((ioBind (ioReturn (S (S (S (S Z)))))) (lambda (v)
      ((ioBind (printNat v)) (lambda (_do0)
        (printSchemeRepr (intToNat (intS (intS (intS intZ)))))))))))
  )
    main))
