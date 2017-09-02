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
    (times (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((('Z) n)
            Z)
          ((('S m) n)
            ((plus n) ((times m) n)))))))
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
    (Pair (lambda (_x5)
      (lambda (_x6)
        `(Pair ,_x5 ,_x6))))
    (MkPair (lambda (a)
      (lambda (b)
        (lambda (_x7)
          (lambda (_x8)
            `(MkPair ,a ,b ,_x7 ,_x8))))))
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
    (Either (lambda (_x11)
      (lambda (_x12)
        `(Either ,_x11 ,_x12))))
    (Left (lambda (a)
      (lambda (b)
        (lambda (_x13)
          `(Left ,a ,b ,_x13)))))
    (Right (lambda (a)
      (lambda (b)
        (lambda (_x14)
          `(Right ,a ,b ,_x14)))))
    (id (lambda (a)
      (lambda (x)
        x)))
    (Fin (lambda (_x15)
      `(Fin ,_x15)))
    (FZ (lambda (n)
      `(FZ ,n)))
    (FS (lambda (n)
      (lambda (_x16)
        `(FS ,n ,_x16))))
    (Vect (lambda (_x17)
      (lambda (_x18)
        `(Vect ,_x17 ,_x18))))
    (VN (lambda (a)
      `(VN ,a)))
    (VC (lambda (n)
      (lambda (a)
        (lambda (x)
          (lambda (xs)
            `(VC ,n ,a ,x ,xs))))))
    (isZero (lambda (_e0)
      (match (list _e0)
        ((('Z))
          True)
        ((('S n))
          False))))
    (f (lambda (_e0)
      (match (list _e0)
        ((('Bool))
          not_TT)
        ((('Nat))
          isZero)
        ((a)
          (lambda (x)
            False)))))
    (main ((f Bool) False))
  )
    main))
