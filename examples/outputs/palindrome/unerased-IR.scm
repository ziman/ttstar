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
    (Maybe (lambda (e0)
      `(Maybe ,e0)))
    (Nothing (lambda (e0)
      `(Nothing ,e0)))
    (Just (curried-lambda (e0 e1)
      `(Just ,e0 ,e1)))
    (not_TT (lambda (_pv0)
      (rts-case _pv0
        ((F) T)
        ((T) F))))
    (Id (curried-lambda (e0 e1 e2)
      `(Id ,e0 ,e1 ,e2)))
    (Refl (curried-lambda (e0 e1)
      `(Refl ,e0 ,e1)))
    (id (lambda (a)
      (lambda (x)
        x)))
    (subst (curried-lambda (_pv0 _pv1 _pv2 _pv3 _pv4)
      (lambda (w)
        w)))
    (cong (curried-lambda (_pv0 _pv1 _pv2 _pv3 _pv4 _pv5)
      ((Refl _pv1) (_pv2 _pv3))))
    (one (lambda (x)
      ((Cons x) Nil)))
    (app (curried-lambda (_pv0 _pv1)
      (rts-case _pv0
        ((Cons _pv2 _pv3) ((Cons _pv2) ((app _pv3) _pv1)))
        ((Nil) _pv1))))
    (appRightNeutral (lambda (_pv0)
      (rts-case _pv0
        ((Cons _pv1 _pv2) ((((((cong List) List) (Cons _pv1)) _pv2) ((app _pv2) Nil)) (appRightNeutral _pv2)))
        ((Nil) ((Refl List) Nil)))))
    (appAssoc (curried-lambda (_pv0 _pv1 _pv2)
      (rts-case _pv0
        ((Cons _pv3 _pv4) ((((((cong List) List) (Cons _pv3)) ((app ((app _pv4) _pv1)) _pv2)) ((app _pv4) ((app _pv1) _pv2))) (((appAssoc _pv4) _pv1) _pv2)))
        ((Nil) ((Refl List) ((app _pv1) _pv2))))))
    (Rev (lambda (e0)
      `(Rev ,e0)))
    (RNil `(RNil))
    (RSnoc (curried-lambda (e0 e1 e2)
      `(RSnoc ,e0 ,e1 ,e2)))
    (rev_ (curried-lambda (_pv0 _pv1 _pv2)
      (rts-case _pv2
        ((Cons _pv3 _pv4) ((((((subst List) Rev) ((app ((app _pv0) (one _pv3))) _pv4)) ((app _pv0) ((Cons _pv3) _pv4))) (((appAssoc _pv0) (one _pv3)) _pv4)) (((rev_ ((app _pv0) (one _pv3))) (((RSnoc _pv0) _pv3) _pv1)) _pv4)))
        ((Nil) ((((((subst List) Rev) _pv0) ((app _pv0) Nil)) (appRightNeutral _pv0)) _pv1)))))
    (rev (lambda (xs)
      (((rev_ Nil) RNil) xs)))
    (reverse_ (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((RNil) Nil)
        ((RSnoc _pv2 _pv3 _pv4) ((Cons _pv3) ((reverse_ _pv2) _pv4))))))
    (reverse_TT (lambda (xs)
      ((reverse_ xs) (rev xs))))
    (V (lambda (e0)
      `(V ,e0)))
    (VNil `(VNil))
    (VOne (lambda (e0)
      `(VOne ,e0)))
    (VTwo (curried-lambda (e0 e1 e2 e3)
      `(VTwo ,e0 ,e1 ,e2 ,e3)))
    (length (lambda (_pv0)
      (rts-case _pv0
        ((Cons _pv1 _pv2) (S (length _pv2)))
        ((Nil) Z))))
    (index (curried-lambda (_pv0 _pv1 _pv2)
      (rts-case _pv0
        ((S _pv3) (rts-case _pv3
          ((S _pv4) (rts-case _pv1
            ((Cons _pv5 _pv6) (rts-case _pv2
              ((Cons _pv7 _pv8) ((Cons _pv5) ((app (((index _pv4) _pv6) _pv8)) (one _pv7))))))))
          ((Z) (rts-case _pv1
            ((Cons _pv4 _pv5) (rts-case _pv2
              ((Cons _pv6 _pv7) ((Cons _pv4) Nil))))))
          (_ (rts-case _pv1
            ((Nil) (rts-case _pv2
              ((Nil) Nil)))))))
        ((Z) Nil))))
    (build (curried-lambda (_pv0 _pv1 _pv2)
      (rts-case _pv0
        ((S _pv3) (rts-case _pv3
          ((S _pv4) (rts-case _pv1
            ((Cons _pv5 _pv6) (rts-case _pv2
              ((Cons _pv7 _pv8) ((((VTwo _pv5) (((index _pv4) _pv6) _pv8)) (((build _pv4) _pv6) _pv8)) _pv7))))))
          ((Z) (rts-case _pv1
            ((Cons _pv4 _pv5) (rts-case _pv2
              ((Cons _pv6 _pv7) (VOne _pv4))))))
          (_ (rts-case _pv1
            ((Nil) (rts-case _pv2
              ((Nil) VNil)))))))
        ((Z) VNil))))
    (eq (lambda (e0)
      `(eq ,e0)))
    (toV (lambda (xs)
      ((((((subst List) V) (((index (length xs)) xs) (reverse_TT xs))) xs) (eq xs)) (((build (length xs)) xs) (reverse_TT xs)))))
    (IsPalindrome (lambda (e0)
      `(IsPalindrome ,e0)))
    (PNil `(PNil))
    (POne (lambda (e0)
      `(POne ,e0)))
    (PTwo (curried-lambda (e0 e1 e2)
      `(PTwo ,e0 ,e1 ,e2)))
    (decEq (curried-lambda (_pv0 _pv1)
      (rts-case _pv0
        ((F) (rts-case _pv1
          ((F) ((Just (((Id B) F) F)) ((Refl B) F)))
          ((T) (Nothing (((Id B) F) T)))))
        ((T) (rts-case _pv1
          ((F) (Nothing (((Id B) T) F)))
          ((T) ((Just (((Id B) T) T)) ((Refl B) T))))))))
    (isPalinV (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((VNil) ((Just (IsPalindrome Nil)) PNil))
        ((VOne _pv2) ((Just (IsPalindrome ((Cons _pv2) Nil))) (POne _pv2)))
        ((VTwo _pv2 _pv3 _pv4 _pv5) 
          (letrec ((isPalinV_ (curried-lambda (_pv6 _pv7 _pv8 _pv9 _pv10 _pv11)
            (rts-case _pv10
              ((Just _pv12 _pv13) (rts-case _pv11
                ((Just _pv14 _pv15) ((Just (IsPalindrome ((Cons _pv6) ((app _pv8) (one _pv6))))) (((PTwo _pv6) _pv8) _pv15)))))
              (_ (Nothing (IsPalindrome ((Cons _pv6) ((app _pv8) (one _pv7))))))))))
            ((((((isPalinV_ _pv2) _pv5) _pv3) _pv4) ((decEq _pv2) _pv5)) ((isPalinV _pv3) _pv4)))))))
    (isPalindrome (lambda (xs)
      ((isPalinV xs) (toV xs))))
    (genList (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((S _pv2) ((Cons _pv0) ((genList (not_TT _pv0)) _pv2)))
        ((Z) Nil))))
    (isJust (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((Just _pv2 _pv3) T)
        ((Nothing _pv2) F))))
    (main 
      (letrec* (
        (inputSize (rts-arg-peano 'Z 'S 0))
        (inputList ((genList T) inputSize))
      ) ((isJust (IsPalindrome inputList)) (isPalindrome inputList))))
  ) main))
(newline)
