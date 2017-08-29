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
    (B `(B))
    (T `(T))
    (F `(F))
    (List `(List))
    (Cons (curried-lambda (e0 e1)
      `(Cons ,e0 ,e1)))
    (Nil `(Nil))
    (not_TT (lambda (_pv0)
      (rts-case _pv0
        ((F) T)
        ((T) F))))
    (input (rts-arg-peano 'Z 'S 0))
    (genList (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((S _pv2) ((Cons _pv0) ((genList (not_TT _pv0)) _pv2)))
        ((Z) Nil))))
    (Eq (curried-lambda (e0 e1 e2)
      `(Eq ,e0 ,e1 ,e2)))
    (Refl (curried-lambda (e0 e1)
      `(Refl ,e0 ,e1)))
    (Maybe (lambda (e0)
      `(Maybe ,e0)))
    (Nothing (lambda (e0)
      `(Nothing ,e0)))
    (Just (curried-lambda (e0 e1)
      `(Just ,e0 ,e1)))
    (semiDecEqB (curried-lambda (_pv0 _pv1)
      (rts-case _pv0
        ((F) (rts-case _pv1
          ((F) ((Just (((Eq B) F) F)) ((Refl B) F)))
          ((T) (Nothing (((Eq B) F) T)))))
        ((T) (rts-case _pv1
          ((F) (Nothing (((Eq B) T) F)))
          ((T) ((Just (((Eq B) T) T)) ((Refl B) T))))))))
    (semiDecEq (curried-lambda (_pv0 _pv1)
      (rts-case _pv0
        ((Cons _pv2 _pv3) (rts-case _pv1
          ((Cons _pv4 _pv5) 
            (letrec ((semiDecEq_ (curried-lambda (_pv6 _pv7 _pv8 _pv9 _pv10 _pv11)
              (rts-case _pv10
                ((Nothing _pv12) (Nothing (((Eq List) ((Cons _pv6) _pv8)) ((Cons _pv7) _pv9))))
                (_ (rts-case _pv11
                  ((Nothing _pv12) (Nothing (((Eq List) ((Cons _pv6) _pv8)) ((Cons _pv7) _pv9))))
                  (_ ((Just (((Eq List) ((Cons _pv6) _pv8)) ((Cons _pv6) _pv8))) ((Refl List) ((Cons _pv6) _pv8))))))))))
              ((((((semiDecEq_ _pv2) _pv4) _pv3) _pv5) ((semiDecEqB _pv2) _pv4)) ((semiDecEq _pv3) _pv5))))
          ((Nil) (Nothing (((Eq List) ((Cons _pv2) _pv3)) Nil)))))
        ((Nil) (rts-case _pv1
          ((Cons _pv2 _pv3) (Nothing (((Eq List) Nil) ((Cons _pv2) _pv3))))
          ((Nil) ((Just (((Eq List) Nil) Nil)) ((Refl List) Nil))))))))
    (sampleList ((genList T) input))
    (main ((semiDecEq sampleList) sampleList))
  ) main))
(newline)
