(import (chicken process-context))

(define-syntax curried-lambda
  (syntax-rules ()
    ((curried-lambda () body) body)
    ((curried-lambda (x . xs) body)
      (lambda (x) (curried-lambda xs body)))))

(define-syntax rts-unpack
  (syntax-rules ()
    ((rts-unpack xs () rhs) rhs)
    ((rts-unpack xs (v . vs) rhs)
      (let ((v (car xs)) (rest (cdr xs)))
        (rts-unpack rest vs rhs)))))

(define-syntax rts-case-int
  (syntax-rules (_)
    ((rts-case-int tag args)
     (error "pattern match failure" (list tag args)))
    ((rts-case-int tag args (_ rhs) . rest)
     rhs)
    ((rts-case-int tag args ((_ . pvs) rhs) . rest)
     (rts-unpack args pvs rhs))
    ((rts-case-int tag args ((cn . pvs) rhs) . rest)
     (if (eq? tag 'cn)
         (rts-unpack args pvs rhs)
         (rts-case-int tag args . rest)))))

(define-syntax rts-case
  (syntax-rules ()
    ((rts-case s . alts) (rts-case-int (car s) (cdr s) . alts))))

(define Type '(Type))

(define (number->peano z s i)
  (if (= i 0)
    (list z)
    (list s (number->peano z s (- i 1)))))

(define (rts-arg-peano z s i)
  (number->peano z s (string->number
                       (list-ref (command-line-arguments) i))))

(define (rts-arg-read i)
  (read (open-input-string
          (list-ref (command-line-arguments) i))))

(display 
  (letrec* (
    (Z `(Z))
    (S (lambda (e0)
      `(S ,e0)))
    (True `(True))
    (False `(False))
    (I `(I))
    (O `(O))
    (N `(N))
    (C (curried-lambda (e0 e1)
      `(C ,e0 ,e1)))
    (TB (curried-lambda (e0 e1)
      `(TB ,e0 ,e1)))
    (adb (curried-lambda (_pv0 _pv1 _pv2)
      (rts-case _pv0
        ((I) (rts-case _pv1
          ((I) (rts-case _pv2
            ((I) ((TB I) I))
            ((O) ((TB I) O))))
          ((O) (rts-case _pv2
            ((I) ((TB I) O))
            ((O) ((TB O) I))))))
        ((O) (rts-case _pv1
          ((I) (rts-case _pv2
            ((I) ((TB I) O))
            ((O) ((TB O) I))))
          ((O) (rts-case _pv2
            ((I) ((TB O) I))
            ((O) ((TB O) O)))))))))
    (add_ (curried-lambda (_pv0 _pv1 _pv2)
      (rts-case _pv1
        ((C _pv3 _pv4) (rts-case _pv2
          ((C _pv5 _pv6) 
            (letrec ((f (lambda (_pv7)
              (rts-unpack (cdr _pv7) (_pv8 _pv9)
                ((C _pv9) (((add_ _pv8) _pv4) _pv6))))))
              (f (((adb _pv0) _pv3) _pv5))))))
        ((N) ((C _pv0) N)))))
    (add (lambda (bx)
      (lambda (by)
        (((add_ O) bx) by))))
    (inputSize (rts-arg-peano 'Z 'S 0))
    (mkBin (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((Z) N)
        (_ (rts-case _pv0
          ((False) (rts-case _pv1
            ((S _pv2) ((C O) ((mkBin True) _pv2)))))
          ((True) (rts-case _pv1
            ((S _pv2) ((C I) ((mkBin False) _pv2))))))))))
    (main ((add ((mkBin True) inputSize)) ((mkBin False) inputSize)))
  ) main))
(newline)
