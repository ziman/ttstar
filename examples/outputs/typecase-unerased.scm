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
    (Fin (lambda (_x13)
      `(Fin ,_x13)))
    (FZ (lambda (n)
      `(FZ ,n)))
    (FS (lambda (n)
      (lambda (_x14)
        `(FS ,n ,_x14))))
    (Vect (lambda (_x15)
      (lambda (_x16)
        `(Vect ,_x15 ,_x16))))
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
