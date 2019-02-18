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
    (MkUnit `(MkUnit))
    (not_TT (lambda (_pv0)
      (rts-case _pv0
        ((F) T)
        ((T) F))))
    (other (not_TT 
      (letrec ((_cf0 (curried-lambda (_pv0 _pv1)
        (rts-case _pv0
          ((F) _pv1)
          ((T) (rts-case _pv1
            ((F) T)
            ((T) F)))))))
        ((_cf0 (not_TT F)) T))))
    (main (not_TT 
      (letrec ((f (curried-lambda (_pv0 _pv1)
        (rts-case _pv0
          ((F) MkUnit)
          ((T) (rts-case _pv1
            ((F) other)
            ((T) F)))))))
        ((f (not_TT F)) T))))
  ) main))
(newline)
