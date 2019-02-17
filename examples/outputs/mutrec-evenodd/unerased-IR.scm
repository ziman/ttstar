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
    (plus (curried-lambda (_pv0 _pv1)
      (rts-case _pv0
        ((S _pv2) (S ((plus _pv2) _pv1)))
        ((Z) _pv1))))
    (times (curried-lambda (_pv0 _pv1)
      (rts-case _pv0
        ((S _pv2) ((plus _pv1) ((times _pv2) _pv1)))
        ((Z) Z))))
    (Bool `(Bool))
    (True `(True))
    (False `(False))
    (not_TT (lambda (_pv0)
      (rts-case _pv0
        ((False) True)
        ((True) False))))
    (Unit `(Unit))
    (MkUnit `(MkUnit))
    (Pair (curried-lambda (e0 e1)
      `(Pair ,e0 ,e1)))
    (MkPair (curried-lambda (e0 e1 e2 e3)
      `(MkPair ,e0 ,e1 ,e2 ,e3)))
    (fst (curried-lambda (_pv0 _pv1 _pv2)
      (rts-unpack (cdr _pv2) (_pv3 _pv4 _pv5 _pv6)
        _pv5)))
    (snd (curried-lambda (_pv0 _pv1 _pv2)
      (rts-unpack (cdr _pv2) (_pv3 _pv4 _pv5 _pv6)
        _pv6)))
    (Either (curried-lambda (e0 e1)
      `(Either ,e0 ,e1)))
    (Left (curried-lambda (e0 e1 e2)
      `(Left ,e0 ,e1 ,e2)))
    (Right (curried-lambda (e0 e1 e2)
      `(Right ,e0 ,e1 ,e2)))
    (id (lambda (a)
      (lambda (x)
        x)))
    (Fin (lambda (e0)
      `(Fin ,e0)))
    (FZ (lambda (e0)
      `(FZ ,e0)))
    (FS (curried-lambda (e0 e1)
      `(FS ,e0 ,e1)))
    (Vect (curried-lambda (e0 e1)
      `(Vect ,e0 ,e1)))
    (VN (lambda (e0)
      `(VN ,e0)))
    (VC (curried-lambda (e0 e1 e2 e3)
      `(VC ,e0 ,e1 ,e2 ,e3)))
    (List (lambda (e0)
      `(List ,e0)))
    (Nil (lambda (e0)
      `(Nil ,e0)))
    (Cons (curried-lambda (e0 e1 e2)
      `(Cons ,e0 ,e1 ,e2)))
    (even (lambda (_pv0)
      (rts-case _pv0
        ((S _pv1) 
          (letrec ((odd (lambda (_pv2)
            (rts-case _pv2
              ((S _pv3) (even _pv3))
              ((Z) False)))))
            (odd _pv1)))
        ((Z) True))))
    (main (even (S (S (S (S (S Z)))))))
  ) main))
(newline)
