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
    (True `(True))
    (False `(False))
    (I `(I))
    (O `(O))
    (N `(N))
    (C (lambda (lsb)
      (lambda (rest)
        `(C ,lsb ,rest))))
    (TB (lambda (hi)
      (lambda (lo)
        `(TB ,hi ,lo))))
    (adb (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((('O) ('O) ('O))
              ((TB O) O))
            ((('I) ('O) ('O))
              ((TB O) I))
            ((('O) ('I) ('O))
              ((TB O) I))
            ((('O) ('O) ('I))
              ((TB O) I))
            ((('I) ('I) ('O))
              ((TB I) O))
            ((('I) ('O) ('I))
              ((TB I) O))
            ((('O) ('I) ('I))
              ((TB I) O))
            ((('I) ('I) ('I))
              ((TB I) I)))))))
    (add_ (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((cb ('N) ('N))
              ((C cb) N))
            ((cb ('C xb xn) ('C yb yn))
              (letrec* ((f (lambda (_e0)
                (match (list _e0)
                  (((_ hi lo))
                    ((C lo) (((add_ hi) xn) yn)))))))
                (f (((adb cb) xb) yb)))))))))
    (inputSize (rts-arg-peano 'Z 'S 0))
    (mkBin (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((b ('Z))
            N)
          ((('True) ('S n))
            ((C I) ((mkBin False) n)))
          ((('False) ('S n))
            ((C O) ((mkBin True) n)))))))
  )
    (((add_ O) ((mkBin True) inputSize)) ((mkBin False) inputSize))))
