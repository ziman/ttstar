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
    (Bool `(Bool))
    (T `(T))
    (F `(F))
    (List `(List))
    (Nil `(Nil))
    (Cons (curried-lambda (e0 e1)
      `(Cons ,e0 ,e1)))
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
    (main (reverse_TT ((Cons T) ((Cons F) ((Cons T) ((Cons F) Nil))))))
  ) main))
(newline)
