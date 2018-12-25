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
    (Plus (curried-lambda (e0 e1)
      `(Plus ,e0 ,e1)))
    (id (lambda (_pv0)
      (rts-case _pv0
        ((S _pv1) 
          (letrec ((result (S _pv1)))
            result))
        ((Z) Z))))
    (const_3 (lambda (x)
      (S (S (S Z)))))
    (two (S (S Z)))
    (f (lambda (g)
      (lambda (z)
        (lambda (h)
          (lambda (w)
            ((Plus (g z)) (h w)))))))
    (apply_TT (lambda (f)
      (lambda (x)
        (f x))))
    (test_1 ((Plus ((apply_TT id) (S (S Z)))) ((apply_TT const_3) two)))
    (test_2 ((((f id) (S (S Z))) const_3) (S Z)))
    (main ((Plus test_1) test_2))
  ) main))
(newline)
