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
    (T `(T))
    (F `(F))
    (Nil `(Nil))
    (Cons (curried-lambda (e0 e1)
      `(Cons ,e0 ,e1)))
    (RNil `(RNil))
    (RSnoc (curried-lambda (e0 e1)
      `(RSnoc ,e0 ,e1)))
    (rev_ (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((Cons _pv2 _pv3) ((rev_ ((RSnoc _pv2) _pv0)) _pv3))
        ((Nil) _pv0))))
    (rev (lambda (xs)
      ((rev_ RNil) xs)))
    (reverse_ (lambda (_pv0)
      (rts-case _pv0
        ((RNil) Nil)
        ((RSnoc _pv1 _pv2) ((Cons _pv1) (reverse_ _pv2))))))
    (reverse_TT (lambda (xs)
      (reverse_ (rev xs))))
    (main (reverse_TT ((Cons T) ((Cons F) ((Cons T) ((Cons F) Nil))))))
  ) main))
(newline)
