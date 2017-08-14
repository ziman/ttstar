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
    (MkUnit `(MkUnit))
    (MkPair (curried-lambda (e0 e1)
      `(MkPair ,e0 ,e1)))
    (snd (lambda (_pv0)
      (rts-case _pv0
        ((_ _pv1 _pv2) _pv2))))
    (MkSt (lambda (e0)
      `(MkSt ,e0)))
    (runState (lambda (_pv0)
      (rts-case _pv0
        ((_ _pv1) _pv1))))
    (execState (lambda (x)
      (lambda (s)
        (snd ((runState x) s)))))
    (stReturn (lambda (x)
      (MkSt (lambda (s)
        ((MkPair s) x)))))
    (stBind (curried-lambda (_pv0 _pv1)
      (rts-case _pv0
        ((_ _pv2) (letrec* (
          (stBind3 (curried-lambda (_pv3 _pv4)
            (rts-case _pv4
              ((_ _pv5) (_pv5 _pv3)))))
          (stBind2 (curried-lambda (_pv3 _pv4)
            (rts-case _pv4
              ((_ _pv5 _pv6) ((stBind3 _pv5) (_pv3 _pv6))))))
        )
          (MkSt (lambda (s)
            ((stBind2 _pv1) (_pv2 s)))))))))
    (ioReturn (lambda (x)
      (stReturn x)))
    (ioBind (lambda (x)
      (lambda (y)
        ((stBind x) y))))
    (ioWrapImpure (lambda (impureF)
      (MkSt (lambda (w)
        ((MkPair w) (impureF MkUnit))))))
    (unsafePerformIO (lambda (x)
      (letrec ((TheWorld (error "postulate")))
        ((execState x) TheWorld))))
    (intS (lambda (x) (+ x 1)))
    (intZ 0)
    (printSchemeRepr (lambda (x)
      (letrec ((nativePrint print))
        (ioWrapImpure (lambda (delayToken)
          (nativePrint x))))))
    (natToInt (lambda (_pv0)
      (rts-case _pv0
        ((S _pv1) (intS (natToInt _pv1)))
        ((Z) intZ))))
    (intToNat (lambda (x) (number->peano 'Z 'S x)))
    (printNat (lambda (x)
      (printSchemeRepr (natToInt x))))
    (main (unsafePerformIO ((ioBind (ioReturn (S (S (S (S Z)))))) (lambda (v)
      ((ioBind (printNat v)) (lambda (_0)
        (printSchemeRepr (intToNat (intS (intS (intS intZ)))))))))))
  )
    main))
(newline)
