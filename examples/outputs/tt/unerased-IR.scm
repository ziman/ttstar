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

(print
  (letrec* (
    (Nat `(Nat))
    (Z `(Z))
    (S (lambda (e0)
      `(S ,e0)))
    (plus (curried-lambda (_pv0 _pv1)
      (rts-case _pv0
        ((S _pv2) (S ((plus _pv2) _pv1)))
        ((Z) _pv1))))
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
      (rts-case _pv2
        ((_ _pv3 _pv4 _pv5 _pv6) _pv5))))
    (snd (curried-lambda (_pv0 _pv1 _pv2)
      (rts-case _pv2
        ((_ _pv3 _pv4 _pv5 _pv6) _pv6))))
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
    (TT (lambda (e0)
      `(TT ,e0)))
    (V (curried-lambda (e0 e1)
      `(V ,e0 ,e1)))
    (Lam (curried-lambda (e0 e1)
      `(Lam ,e0 ,e1)))
    (App (curried-lambda (e0 e1 e2)
      `(App ,e0 ,e1 ,e2)))
    (env (curried-lambda (_pv0 _pv1 _pv2 _pv3)
      (rts-case _pv2
        ((VC _pv4 _pv5 _pv6 _pv7) (rts-case _pv3
          ((FS _pv8 _pv9) ((((env _pv8) _pv1) _pv7) _pv9))
          ((FZ _pv8) _pv6))))))
    (extendMap (curried-lambda (_pv0 _pv1 _pv2 _pv3)
      (rts-case _pv3
        ((FS _pv4 _pv5) ((FS _pv1) (_pv2 _pv5)))
        ((FZ _pv4) (FZ _pv1)))))
    (mapVars (curried-lambda (_pv0 _pv1 _pv2 _pv3)
      (rts-case _pv3
        ((App _pv4 _pv5 _pv6) (((App _pv1) ((((mapVars _pv0) _pv1) _pv2) _pv5)) ((((mapVars _pv0) _pv1) _pv2) _pv6)))
        ((Lam _pv4 _pv5) ((Lam _pv1) ((((mapVars (S _pv0)) (S _pv1)) (((extendMap _pv0) _pv1) _pv2)) _pv5)))
        ((V _pv4 _pv5) ((V _pv1) (_pv2 _pv5))))))
    (extendSubst (curried-lambda (_pv0 _pv1 _pv2 _pv3)
      (rts-case _pv3
        ((FS _pv4 _pv5) ((((mapVars _pv1) (S _pv1)) (FS _pv1)) (_pv2 _pv5)))
        ((FZ _pv4) ((V (S _pv1)) (FZ _pv1))))))
    (substVars (curried-lambda (_pv0 _pv1 _pv2 _pv3)
      (rts-case _pv3
        ((App _pv4 _pv5 _pv6) (((App _pv1) ((((substVars _pv0) _pv1) _pv2) _pv5)) ((((substVars _pv0) _pv1) _pv2) _pv6)))
        ((Lam _pv4 _pv5) ((Lam _pv1) ((((substVars (S _pv0)) (S _pv1)) (((extendSubst _pv0) _pv1) _pv2)) _pv5)))
        ((V _pv4 _pv5) (_pv2 _pv5)))))
    (testTm (((App (S Z)) ((Lam (S Z)) (((App (S (S Z))) ((V (S (S Z))) (FZ (S Z)))) ((V (S (S Z))) ((FS (S Z)) (FZ Z)))))) ((Lam (S Z)) (((App (S (S Z))) ((V (S (S Z))) ((FS (S Z)) (FZ Z)))) ((V (S (S Z))) (FZ (S Z)))))))
    (example1 ((((substVars (S Z)) Z) (((env (S Z)) Z) ((((VC Z) (TT Z)) ((Lam Z) ((V (S Z)) (FZ Z)))) (VN (TT Z))))) testTm))
    (substTop (curried-lambda (_pv0 _pv1 _pv2)
      (rts-case _pv2
        ((FS _pv3 _pv4) ((V _pv0) _pv4))
        ((FZ _pv3) _pv1))))
    (nf (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((App _pv2 _pv3 _pv4) (letrec ((g (lambda (_pv5)
          (rts-case _pv5
            ((Lam _pv6 _pv7) ((nf _pv0) ((((substVars (S _pv0)) _pv0) ((substTop _pv0) ((nf _pv0) _pv4))) _pv7)))
            (_ (((App _pv0) _pv5) ((nf _pv0) _pv4)))))))
          (g ((nf _pv0) _pv3))))
        ((Lam _pv2 _pv3) ((Lam _pv0) ((nf (S _pv0)) _pv3)))
        ((V _pv2 _pv3) ((V _pv0) _pv3)))))
    (example2 ((nf (S Z)) testTm))
    (Result `(Result))
    (R (curried-lambda (e0 e1)
      `(R ,e0 ,e1)))
    (main ((R example1) example2))
  )
    main))
