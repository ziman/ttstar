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
    (Nat `(Nat))
    (Z `(Z))
    (S (lambda (e0)
      `(S ,e0)))
    (plus (curried-lambda (_pv0 _pv1)
      (rts-case _pv0
        ((S _pv2) (S ((plus _pv2) _pv1)))
        ((Z) _pv1))))
    (times (curried-lambda (_pv0 _pv1)
      (rts-case _pv0
        ((S _pv2) ((plus _pv1) ((times _pv2) _pv1)))
        ((Z) Z))))
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
      (rts-unpack (cdr _pv2) (_pv3 _pv4 _pv5 _pv6)
        _pv5)))
    (snd (curried-lambda (_pv0 _pv1 _pv2)
      (rts-unpack (cdr _pv2) (_pv3 _pv4 _pv5 _pv6)
        _pv6)))
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
    (List (lambda (e0)
      `(List ,e0)))
    (Nil (lambda (e0)
      `(Nil ,e0)))
    (Cons (curried-lambda (e0 e1 e2)
      `(Cons ,e0 ,e1 ,e2)))
    (Id (curried-lambda (e0 e1 e2)
      `(Id ,e0 ,e1 ,e2)))
    (Refl (curried-lambda (e0 e1)
      `(Refl ,e0 ,e1)))
    (subst (curried-lambda (_pv0 _pv1 _pv2 _pv3 _pv4)
      (lambda (z)
        z)))
    (Bit (lambda (e0)
      `(Bit ,e0)))
    (I `(I))
    (O `(O))
    (double (lambda (_pv0)
      (rts-case _pv0
        ((S _pv1) (S (S (double _pv1))))
        ((Z) Z))))
    (Bin (curried-lambda (e0 e1)
      `(Bin ,e0 ,e1)))
    (N `(N))
    (C (curried-lambda (e0 e1 e2 e3 e4)
      `(C ,e0 ,e1 ,e2 ,e3 ,e4)))
    (TwoBits (curried-lambda (e0 e1 e2)
      `(TwoBits ,e0 ,e1 ,e2)))
    (TB (curried-lambda (e0 e1 e2 e3 e4 e5 e6 e7)
      `(TB ,e0 ,e1 ,e2 ,e3 ,e4 ,e5 ,e6 ,e7)))
    (adb (curried-lambda (_pv0 _pv1 _pv2 _pv3 _pv4 _pv5)
      (rts-case _pv3
        ((I) (rts-case _pv4
          ((I) (rts-case _pv5
            ((I) ((((((((TB (S Z)) (S Z)) (S Z)) (S Z)) I) (S Z)) I) ((Refl Nat) (S (S (S Z))))))
            ((O) ((((((((TB (S Z)) (S Z)) Z) (S Z)) I) Z) O) ((Refl Nat) (S (S Z)))))))
          ((O) (rts-case _pv5
            ((I) ((((((((TB (S Z)) Z) (S Z)) (S Z)) I) Z) O) ((Refl Nat) (S (S Z)))))
            ((O) ((((((((TB (S Z)) Z) Z) Z) O) (S Z)) I) ((Refl Nat) (S Z))))))))
        ((O) (rts-case _pv4
          ((I) (rts-case _pv5
            ((I) ((((((((TB Z) (S Z)) (S Z)) (S Z)) I) Z) O) ((Refl Nat) (S (S Z)))))
            ((O) ((((((((TB Z) (S Z)) Z) Z) O) (S Z)) I) ((Refl Nat) (S Z))))))
          ((O) (rts-case _pv5
            ((I) ((((((((TB Z) Z) (S Z)) Z) O) (S Z)) I) ((Refl Nat) (S Z))))
            ((O) ((((((((TB Z) Z) Z) Z) O) Z) O) ((Refl Nat) Z))))))))))
    (add_ (curried-lambda (_pv0 _pv1 _pv2 _pv3 _pv4 _pv5 _pv6)
      (rts-case _pv5
        ((N) (rts-case _pv6
          ((N) (((((C Z) _pv1) _pv4) Z) N))
          (_ (rts-unpack (cdr _pv0) (_pv7)
            (rts-case _pv5
              ((C _pv8 _pv9 _pv10 _pv11 _pv12) (rts-case _pv6
                ((C _pv13 _pv14 _pv15 _pv16 _pv17) 
                  (letrec ((f (lambda (_pv18)
                    (rts-unpack (cdr _pv18) (_pv19 _pv20 _pv21 _pv22 _pv23 _pv24 _pv25 _pv26)
                      
                        (letrec* (
                          (x ((plus _pv24) (double ((plus _pv22) ((plus _pv11) _pv16)))))
                          (y ((plus _pv1) ((plus ((plus _pv9) (double _pv11))) ((plus _pv14) (double _pv16)))))
                          (eq `(eq))
                        ) ((((((subst Nat) (Bin (S (S _pv7)))) ((plus _pv24) (double ((plus _pv22) ((plus _pv11) _pv16))))) ((plus _pv1) ((plus ((plus _pv9) (double _pv11))) ((plus _pv14) (double _pv16))))) eq) (((((C (S _pv7)) _pv24) _pv25) ((plus _pv22) ((plus _pv11) _pv16))) (((((((add_ _pv7) _pv22) _pv11) _pv16) _pv23) _pv12) _pv17))))))))
                    (f ((((((adb _pv1) _pv9) _pv14) _pv4) _pv10) _pv15)))))))))))
        (_ (rts-unpack (cdr _pv0) (_pv7)
          (rts-case _pv5
            ((C _pv8 _pv9 _pv10 _pv11 _pv12) (rts-case _pv6
              ((C _pv13 _pv14 _pv15 _pv16 _pv17) 
                (letrec ((f (lambda (_pv18)
                  (rts-unpack (cdr _pv18) (_pv19 _pv20 _pv21 _pv22 _pv23 _pv24 _pv25 _pv26)
                    
                      (letrec* (
                        (x ((plus _pv24) (double ((plus _pv22) ((plus _pv11) _pv16)))))
                        (y ((plus _pv1) ((plus ((plus _pv9) (double _pv11))) ((plus _pv14) (double _pv16)))))
                        (eq `(eq))
                      ) ((((((subst Nat) (Bin (S (S _pv7)))) ((plus _pv24) (double ((plus _pv22) ((plus _pv11) _pv16))))) ((plus _pv1) ((plus ((plus _pv9) (double _pv11))) ((plus _pv14) (double _pv16))))) eq) (((((C (S _pv7)) _pv24) _pv25) ((plus _pv22) ((plus _pv11) _pv16))) (((((((add_ _pv7) _pv22) _pv11) _pv16) _pv23) _pv12) _pv17))))))))
                  (f ((((((adb _pv1) _pv9) _pv14) _pv4) _pv10) _pv15))))))))))))
    (add (lambda (w)
      (lambda (x)
        (lambda (y)
          (lambda (bx)
            (lambda (by)
              (((((((add_ w) Z) x) y) O) bx) by)))))))
    (inputSize (rts-arg-peano 'Z 'S 0))
    (binVal (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((Z) Z)
        (_ (rts-case _pv0
          ((False) (rts-case _pv1
            ((S _pv2) (double ((binVal True) _pv2)))))
          ((True) (rts-case _pv1
            ((S _pv2) (S (double ((binVal False) _pv2)))))))))))
    (mkBin (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((Z) N)
        (_ (rts-case _pv0
          ((False) (rts-case _pv1
            ((S _pv2) (((((C _pv2) Z) O) ((binVal True) _pv2)) ((mkBin True) _pv2)))))
          ((True) (rts-case _pv1
            ((S _pv2) (((((C _pv2) (S Z)) I) ((binVal False) _pv2)) ((mkBin False) _pv2))))))))))
    (main 
      (letrec* (
        (x ((mkBin True) inputSize))
        (y ((mkBin False) inputSize))
      ) (((((add inputSize) ((binVal True) inputSize)) ((binVal False) inputSize)) x) y)))
  ) main))
(newline)
