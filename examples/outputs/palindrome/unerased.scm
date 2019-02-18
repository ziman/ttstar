(import (chicken process-context))
(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (N `(N))
    (Z `(Z))
    (S (lambda (_x0)
      `(S ,_x0)))
    (B `(B))
    (T `(T))
    (F `(F))
    (List `(List))
    (Cons (lambda (_x1)
      (lambda (_x2)
        `(Cons ,_x1 ,_x2))))
    (Nil `(Nil))
    (Maybe (lambda (_x3)
      `(Maybe ,_x3)))
    (Nothing (lambda (a)
      `(Nothing ,a)))
    (Just (lambda (a)
      (lambda (x)
        `(Just ,a ,x))))
    (not_TT (lambda (_e0)
      (match (list _e0)
        ((('T))
          F)
        ((('F))
          T))))
    (Id (lambda (a)
      (lambda (x)
        (lambda (y)
          `(Id ,a ,x ,y)))))
    (Refl (lambda (a)
      (lambda (x)
        `(Refl ,a ,x))))
    (id (lambda (a)
      (lambda (x)
        x)))
    (subst (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (lambda (_e3)
            (lambda (_e4)
              (match (list _e0 _e1 _e2 _e3 _e4)
                ((a P x _ (_ _ _))
                  (lambda (w)
                    w)))))))))
    (cong (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (lambda (_e3)
            (lambda (_e4)
              (lambda (_e5)
                (match (list _e0 _e1 _e2 _e3 _e4 _e5)
                  ((a b f x _ _)
                    ((Refl b) (f x)))))))))))
    (one (lambda (x)
      ((Cons x) Nil)))
    (app (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((('Nil) ys)
            ys)
          ((('Cons x xs) ys)
            ((Cons x) ((app xs) ys)))))))
    (appRightNeutral (lambda (_e0)
      (match (list _e0)
        ((('Nil))
          ((Refl List) Nil))
        ((('Cons x xs))
          ((((((cong List) List) (Cons x)) xs) ((app xs) Nil)) (appRightNeutral xs))))))
    (appAssoc (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((('Nil) ys zs)
              ((Refl List) ((app ys) zs)))
            ((('Cons x xs) ys zs)
              ((((((cong List) List) (Cons x)) ((app ((app xs) ys)) zs)) ((app xs) ((app ys) zs))) (((appAssoc xs) ys) zs))))))))
    (Rev (lambda (_x11)
      `(Rev ,_x11)))
    (RNil `(RNil))
    (RSnoc (lambda (xs)
      (lambda (x)
        (lambda (rxs)
          `(RSnoc ,xs ,x ,rxs)))))
    (rev_ (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((xs rxs ('Nil))
              ((((((subst List) Rev) xs) ((app xs) Nil)) (appRightNeutral xs)) rxs))
            ((xs rxs ('Cons y ys))
              ((((((subst List) Rev) ((app ((app xs) (one y))) ys)) ((app xs) ((Cons y) ys))) (((appAssoc xs) (one y)) ys)) (((rev_ ((app xs) (one y))) (((RSnoc xs) y) rxs)) ys))))))))
    (rev (lambda (xs)
      (((rev_ Nil) RNil) xs)))
    (reverse_ (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((_ ('RNil))
            Nil)
          ((_ ('RSnoc xs x rxs))
            ((Cons x) ((reverse_ xs) rxs)))))))
    (reverse_TT (lambda (xs)
      ((reverse_ xs) (rev xs))))
    (V (lambda (_x12)
      `(V ,_x12)))
    (VNil `(VNil))
    (VOne (lambda (x)
      `(VOne ,x)))
    (VTwo (lambda (x)
      (lambda (xs)
        (lambda (u)
          (lambda (y)
            `(VTwo ,x ,xs ,u ,y))))))
    (length (lambda (_e0)
      (match (list _e0)
        ((('Nil))
          Z)
        ((('Cons x xs))
          (S (length xs))))))
    (index (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((('Z) xs ys)
              Nil)
            ((('S ('Z)) ('Cons x xs) ('Cons y ys))
              ((Cons x) Nil))
            ((('S ('S n)) ('Cons x xs) ('Cons y ys))
              ((Cons x) ((app (((index n) xs) ys)) (one y))))
            ((('S n) ('Nil) ('Nil))
              Nil))))))
    (build (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((('Z) xs ys)
              VNil)
            ((('S ('Z)) ('Cons x xs) ('Cons y ys))
              (VOne x))
            ((('S ('S n)) ('Cons x xs) ('Cons y ys))
              ((((VTwo x) (((index n) xs) ys)) (((build n) xs) ys)) y))
            ((('S n) ('Nil) ('Nil))
              VNil))))))
    (eq (lambda (xs)
      `(eq ,xs)))
    (toV (lambda (xs)
      ((((((subst List) V) (((index (length xs)) xs) (reverse_TT xs))) xs) (eq xs)) (((build (length xs)) xs) (reverse_TT xs)))))
    (IsPalindrome (lambda (_x17)
      `(IsPalindrome ,_x17)))
    (PNil `(PNil))
    (POne (lambda (b)
      `(POne ,b)))
    (PTwo (lambda (b)
      (lambda (xs)
        (lambda (pf)
          `(PTwo ,b ,xs ,pf)))))
    (decEq (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((('T) ('T))
            ((Just (((Id B) T) T)) ((Refl B) T)))
          ((('F) ('F))
            ((Just (((Id B) F) F)) ((Refl B) F)))
          ((('T) ('F))
            (Nothing (((Id B) T) F)))
          ((('F) ('T))
            (Nothing (((Id B) F) T)))))))
    (isPalinV (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((_ ('VNil))
            ((Just (IsPalindrome Nil)) PNil))
          ((_ ('VOne x))
            ((Just (IsPalindrome ((Cons x) Nil))) (POne x)))
          ((_ ('VTwo x xs v y))
            (letrec* ((isPalinV_ (lambda (_e0)
              (lambda (_e1)
                (lambda (_e2)
                  (lambda (_e3)
                    (lambda (_e4)
                      (lambda (_e5)
                        (match (list _e0 _e1 _e2 _e3 _e4 _e5)
                          ((x _ xs v ('Just _ _) ('Just _ pfV))
                            ((Just (IsPalindrome ((Cons x) ((app xs) (one x))))) (((PTwo x) xs) pfV)))
                          ((x y xs v pfB pfV)
                            (Nothing (IsPalindrome ((Cons x) ((app xs) (one y)))))))))))))))
              ((((((isPalinV_ x) y) xs) v) ((decEq x) y)) ((isPalinV xs) v))))))))
    (isPalindrome (lambda (xs)
      ((isPalinV xs) (toV xs))))
    (genList (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((b ('Z))
            Nil)
          ((b ('S n))
            ((Cons b) ((genList (not_TT b)) n)))))))
    (isJust (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((a ('Just _ x))
            T)
          ((a ('Nothing _))
            F)))))
    (main (letrec* (
      (inputSize (rts-arg-peano 'Z 'S 0))
      (inputList ((genList T) inputSize))
    )
      ((isJust (IsPalindrome inputList)) (isPalindrome inputList))))
  )
    main))
