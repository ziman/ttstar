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
    (FZ `(FZ))
    (FS (lambda (e0)
      `(FS ,e0)))
    (VN `(VN))
    (VC (curried-lambda (e0 e1)
      `(VC ,e0 ,e1)))
    (V (lambda (e0)
      `(V ,e0)))
    (Lam (lambda (e0)
      `(Lam ,e0)))
    (App (curried-lambda (e0 e1)
      `(App ,e0 ,e1)))
    (env (curried-lambda (_pv0 _pv1)
      (rts-case _pv0
        ((VC _pv2 _pv3) (rts-case _pv1
          ((FS _pv4) ((env _pv3) _pv4))
          ((FZ) _pv2))))))
    (extendMap (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((FS _pv2) (FS (_pv0 _pv2)))
        ((FZ) FZ))))
    (mapVars (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((App _pv2 _pv3) ((App ((mapVars _pv0) _pv2)) ((mapVars _pv0) _pv3)))
        ((Lam _pv2) (Lam ((mapVars (extendMap _pv0)) _pv2)))
        ((V _pv2) (V (_pv0 _pv2))))))
    (extendSubst (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((FS _pv2) ((mapVars FS) (_pv0 _pv2)))
        ((FZ) (V FZ)))))
    (substVars (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((App _pv2 _pv3) ((App ((substVars _pv0) _pv2)) ((substVars _pv0) _pv3)))
        ((Lam _pv2) (Lam ((substVars (extendSubst _pv0)) _pv2)))
        ((V _pv2) (_pv0 _pv2)))))
    (testTm ((App (Lam ((App (V FZ)) (V (FS FZ))))) (Lam ((App (V (FS FZ))) (V FZ)))))
    (example1 ((substVars (env ((VC (Lam (V FZ))) VN))) testTm))
    (substTop (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((FS _pv2) (V _pv2))
        ((FZ) _pv0))))
    (nf (lambda (_pv0)
      (rts-case _pv0
        ((App _pv1 _pv2) (letrec ((g (lambda (_pv3)
          (rts-case _pv3
            ((Lam _pv4) (nf ((substVars (substTop (nf _pv2))) _pv4)))
            (_ ((App _pv3) (nf _pv2)))))))
          (g (nf _pv1))))
        ((Lam _pv1) (Lam (nf _pv1)))
        ((V _pv1) (V _pv1)))))
    (example2 (nf testTm))
    (R (curried-lambda (e0 e1)
      `(R ,e0 ,e1)))
    (main ((R example1) example2))
  )
    main))
(newline)
