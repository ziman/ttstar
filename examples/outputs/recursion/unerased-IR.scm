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
    (Bool `(Bool))
    (True `(True))
    (False `(False))
    (Nat `(Nat))
    (Z `(Z))
    (S (lambda (e0)
      `(S ,e0)))
    (Vec (curried-lambda (e0 e1)
      `(Vec ,e0 ,e1)))
    (VNil (lambda (e0)
      `(VNil ,e0)))
    (VCons (curried-lambda (e0 e1 e2 e3)
      `(VCons ,e0 ,e1 ,e2 ,e3)))
    (vlen (curried-lambda (_pv0 _pv1 _pv2)
      (rts-case _pv2
        ((VNil _pv3) Z)
        (_ (rts-unpack (cdr _pv1) (_pv3)
          (rts-case _pv2
            ((VCons _pv4 _pv5 _pv6 _pv7) (S (((vlen _pv0) _pv3) _pv7)))))))))
    (testVec ((((VCons Bool) (S Z)) True) ((((VCons Bool) Z) False) (VNil Bool))))
    (main (((vlen Bool) (S (S Z))) testVec))
  ) main))
(newline)
