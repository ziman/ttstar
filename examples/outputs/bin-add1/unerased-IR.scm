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
    (Nat `(Nat))
    (Z `(Z))
    (S (lambda (e0)
      `(S ,e0)))
    (double (lambda (_pv0)
      (rts-case _pv0
        ((S _pv1) (S (S (double _pv1))))
        ((Z) Z))))
    (Bin (lambda (e0)
      `(Bin ,e0)))
    (N `(N))
    (O (curried-lambda (e0 e1)
      `(O ,e0 ,e1)))
    (I (curried-lambda (e0 e1)
      `(I ,e0 ,e1)))
    (add1 (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((I _pv2 _pv3) ((O (S _pv2)) ((add1 _pv2) _pv3)))
        ((N) ((I Z) N))
        ((O _pv2 _pv3) ((I _pv2) _pv3)))))
    (main ((add1 (S Z)) ((I Z) N)))
  ) main))
(newline)
