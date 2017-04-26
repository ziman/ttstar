(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (Nat `(Nat))
    (Z `(Z))
    (S (lambda (x)
      `(S ,x)))
    (plus (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((('Z) n)
            n)
          ((('S m) n)
            (S ((plus m) n)))))))
    (Bool `(Bool))
    (True `(True))
    (False `(False))
    (not_TT (lambda (_e0)
      (match (list _e0)
        ((('True))
          False)
        ((('False))
          True))))
    (Unit `(Unit))
    (MkUnit `(MkUnit))
    (Pair (lambda (_x3)
      (lambda (_x4)
        `(Pair ,_x3 ,_x4))))
    (MkPair (lambda (a)
      (lambda (b)
        (lambda (_x5)
          (lambda (_x6)
            `(MkPair ,a ,b ,_x5 ,_x6))))))
    (fst (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((a b (_ _ _ x y))
              x))))))
    (snd (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((a b (_ _ _ x y))
              y))))))
    (Either (lambda (_x9)
      (lambda (_x10)
        `(Either ,_x9 ,_x10))))
    (Left (lambda (a)
      (lambda (b)
        (lambda (_x11)
          `(Left ,a ,b ,_x11)))))
    (Right (lambda (a)
      (lambda (b)
        (lambda (_x12)
          `(Right ,a ,b ,_x12)))))
    (id (lambda (a)
      (lambda (x)
        x)))
    (Id (lambda (a)
      (lambda (x)
        (lambda (y)
          `(Id ,a ,x ,y)))))
    (Refl (lambda (a)
      (lambda (x)
        `(Refl ,a ,x))))
    (subst (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (lambda (_e3)
            (lambda (_e4)
              (match (list _e0 _e1 _e2 _e3 _e4)
                ((a P x _ _)
                  (lambda (z)
                    z)))))))))
    (Bit (lambda (_x0)
      `(Bit ,_x0)))
    (I `(I))
    (O `(O))
    (double (lambda (_e0)
      (match (list _e0)
        ((('Z))
          Z)
        ((('S n))
          (S (S (double n)))))))
    (Bin (lambda (width)
      (lambda (value)
        `(Bin ,width ,value))))
    (N `(N))
    (C (lambda (width)
      (lambda (lsbVal)
        (lambda (lsb)
          (lambda (restVal)
            (lambda (rest)
              `(C ,width ,lsbVal ,lsb ,restVal ,rest)))))))
    (TwoBits (lambda (_x2)
      (lambda (_x3)
        (lambda (_x4)
          `(TwoBits ,_x2 ,_x3 ,_x4)))))
    (TB (lambda (c)
      (lambda (x)
        (lambda (y)
          (lambda (hi_)
            (lambda (hi)
              (lambda (lo_)
                (lambda (lo)
                  (lambda (pf)
                    `(TB ,c ,x ,y ,hi_ ,hi ,lo_ ,lo ,pf))))))))))
    (adb (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (lambda (_e3)
            (lambda (_e4)
              (lambda (_e5)
                (match (list _e0 _e1 _e2 _e3 _e4 _e5)
                  ((_ _ _ ('O) ('O) ('O))
                    ((((((((TB Z) Z) Z) Z) O) Z) O) ((Refl Nat) Z)))
                  ((_ _ _ ('I) ('O) ('O))
                    ((((((((TB (S Z)) Z) Z) Z) O) (S Z)) I) ((Refl Nat) (S Z))))
                  ((_ _ _ ('O) ('I) ('O))
                    ((((((((TB Z) (S Z)) Z) Z) O) (S Z)) I) ((Refl Nat) (S Z))))
                  ((_ _ _ ('O) ('O) ('I))
                    ((((((((TB Z) Z) (S Z)) Z) O) (S Z)) I) ((Refl Nat) (S Z))))
                  ((_ _ _ ('I) ('I) ('O))
                    ((((((((TB (S Z)) (S Z)) Z) (S Z)) I) Z) O) ((Refl Nat) (S (S Z)))))
                  ((_ _ _ ('I) ('O) ('I))
                    ((((((((TB (S Z)) Z) (S Z)) (S Z)) I) Z) O) ((Refl Nat) (S (S Z)))))
                  ((_ _ _ ('O) ('I) ('I))
                    ((((((((TB Z) (S Z)) (S Z)) (S Z)) I) Z) O) ((Refl Nat) (S (S Z)))))
                  ((_ _ _ ('I) ('I) ('I))
                    ((((((((TB (S Z)) (S Z)) (S Z)) (S Z)) I) (S Z)) I) ((Refl Nat) (S (S (S Z))))))))))))))
    (add_ (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (lambda (_e3)
            (lambda (_e4)
              (lambda (_e5)
                (lambda (_e6)
                  (match (list _e0 _e1 _e2 _e3 _e4 _e5 _e6)
                    ((_ c _ _ cb ('N) ('N))
                      (((((C Z) c) cb) Z) N))
                    (((_ w) c _ _ cb ('C _ xb_ xb xn_ xn) ('C _ yb_ yb yn_ yn))
                      (letrec* ((f (lambda (_e0)
                        (match (list _e0)
                          ((('TB _ _ _ hi_ hi lo_ lo pf))
                            (letrec* ((eq `(eq)))
                              ((((((subst Nat) (Bin (S (S w)))) ((plus lo_) (double ((plus hi_) ((plus xn_) yn_))))) ((plus c) ((plus ((plus xb_) (double xn_))) ((plus yb_) (double yn_))))) eq) (((((C (S w)) lo_) lo) ((plus hi_) ((plus xn_) yn_))) (((((((add_ w) hi_) xn_) yn_) hi) xn) yn)))))))))
                        (f ((((((adb c) xb_) yb_) cb) xb) yb)))))))))))))
    (add (lambda (w)
      (lambda (x)
        (lambda (y)
          (lambda (bx)
            (lambda (by)
              (((((((add_ w) Z) x) y) O) bx) by)))))))
    (inputSize (rts-arg-peano 'Z 'S 0))
    (binVal (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((b ('Z))
            Z)
          ((('True) ('S n))
            (S (double ((binVal False) n))))
          ((('False) ('S n))
            (double ((binVal True) n)))))))
    (mkBin (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((b ('Z))
            N)
          ((('True) ('S n))
            (((((C n) (S Z)) I) ((binVal False) n)) ((mkBin False) n)))
          ((('False) ('S n))
            (((((C n) Z) O) ((binVal True) n)) ((mkBin True) n)))))))
    (main (letrec* (
      (x ((mkBin True) inputSize))
      (y ((mkBin False) inputSize))
    )
      (((((add inputSize) ((binVal True) inputSize)) ((binVal False) inputSize)) x) y)))
  )
    main))
