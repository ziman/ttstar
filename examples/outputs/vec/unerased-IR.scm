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
    (N `(N))
    (Z `(Z))
    (S (lambda (e0)
      `(S ,e0)))
    (Vec (curried-lambda (e0 e1)
      `(Vec ,e0 ,e1)))
    (Nil (lambda (e0)
      `(Nil ,e0)))
    (Cons (curried-lambda (e0 e1 e2 e3)
      `(Cons ,e0 ,e1 ,e2 ,e3)))
    (plus (curried-lambda (_pv0 _pv1)
      (rts-case _pv0
        ((S _pv2) (S ((plus _pv2) _pv1)))
        ((Z) _pv1))))
    (append_TT (curried-lambda (_pv0 _pv1 _pv2 _pv3 _pv4)
      (rts-case _pv3
        ((Nil _pv5) _pv4)
        (_ (rts-unpack (cdr _pv1) (_pv5)
          (rts-case _pv3
            ((Cons _pv6 _pv7 _pv8 _pv9) ((((Cons _pv0) ((plus _pv5) _pv2)) _pv8) (((((append_TT _pv0) _pv5) _pv2) _pv9) _pv4)))))))))
    (main (((((append_TT N) Z) (S Z)) (Nil N)) ((((Cons N) Z) (S (S (S (S Z))))) (Nil N))))
  ) main))
(newline)
