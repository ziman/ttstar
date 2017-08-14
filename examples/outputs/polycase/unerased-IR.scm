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
    (Mool `(Mool))
    (Q `(Q))
    (W `(W))
    (Bool `(Bool))
    (T `(T))
    (F `(F))
    (Id (curried-lambda (e0 e1 e2)
      `(Id ,e0 ,e1 ,e2)))
    (Refl (curried-lambda (e0 e1)
      `(Refl ,e0 ,e1)))
    (not_TT (lambda (_pv0)
      (rts-case _pv0
        ((F) T)
        ((T) F))))
    (notnot (lambda (_pv0)
      (rts-case _pv0
        ((F) ((Refl Bool) F))
        ((T) ((Refl Bool) T)))))
    (retTy (lambda (_pv0)
      (rts-case _pv0
        ((F) Mool)
        ((T) Bool))))
    (mot (lambda (_pv0)
      (rts-case _pv0
        ((Q) W)
        ((W) Q))))
    (invert (lambda (_pv0)
      (rts-case _pv0
        ((F) mot)
        ((T) not_TT))))
    (invert_ (curried-lambda (_pv0 _pv1)
      (rts-case _pv0
        ((F) (mot _pv1))
        ((T) (not_TT _pv1)))))
    (main ((invert F) Q))
  )
    main))
(newline)
