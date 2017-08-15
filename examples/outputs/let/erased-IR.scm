(define-syntax curried-lambda
  (syntax-rules ()
    ((curried-lambda () body) body)
    ((curried-lambda (x . xs) body)
      (lambda (x) (curried-lambda xs body)))))

(define-syntax rts-unpack
  (syntax-rules ()
    ((rts-unpack xs () rhs) rhs)
    ((rts-unpack xs (v . vs) rhs)
      (let ((v (car xs)))
        (rts-unpack (cdr xs) vs rhs)))))

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
    (plus (curried-lambda (_pv0 _pv1)
      (rts-case _pv0
        ((S _pv2) (S ((plus _pv2) _pv1)))
        ((Z) _pv1))))
    (const (lambda (x)
      (lambda (y)
        x)))
    (main (letrec* (
      (apply_TT (curried-lambda (_pv0 _pv1)
        (rts-case _pv1
          ((S _pv2) (_pv0 (S _pv2)))
          ((Z) (_pv0 Z)))))
      (Q `(Q))
      (three (S (S (S Z))))
    )
      ((plus ((apply_TT (lambda (x)
        x)) (S (S Z)))) ((apply_TT (const Q)) three))))
  )
    main))
(newline)
