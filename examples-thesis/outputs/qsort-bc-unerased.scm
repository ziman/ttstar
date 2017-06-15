(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (Nat `(Nat))
    (Z `(Z))
    (S (lambda (n)
      `(S ,n)))
    (Bool `(Bool))
    (True `(True))
    (False `(False))
    (NList `(NList))
    (Nil `(Nil))
    (Cons (lambda (x)
      (lambda (xs)
        `(Cons ,x ,xs))))
    (someList ((Cons (S (S (S (S (S (S (S (S (S Z)))))))))) ((Cons (S (S (S (S (S Z)))))) ((Cons (S Z)) ((Cons (S (S (S Z)))) ((Cons (S Z)) ((Cons (S (S (S (S (S Z)))))) ((Cons (S (S Z))) Nil))))))))
    (Rel2 (lambda (a)
      '_))
    (Acc (lambda (a)
      (lambda (lt)
        (lambda (x)
          `(Acc ,a ,lt ,x)))))
    (MkAcc (lambda (a)
      (lambda (lt)
        (lambda (x)
          (lambda (acc)
            `(MkAcc ,a ,lt ,x ,acc))))))
    (LE (lambda (_x0)
      (lambda (_x1)
        `(LE ,_x0 ,_x1))))
    (LEZ (lambda (n)
      `(LEZ ,n)))
    (LES (lambda (m)
      (lambda (n)
        (lambda (_x2)
          `(LES ,m ,n ,_x2)))))
    (LT (lambda (x)
      (lambda (y)
        ((LE (S x)) y))))
    (leRefl (lambda (_e0)
      (match (list _e0)
        ((('Z))
          (LEZ Z))
        ((('S x))
          (((LES x) x) (leRefl x))))))
    (leTrans (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (lambda (_e3)
            (lambda (_e4)
              (match (list _e0 _e1 _e2 _e3 _e4)
                ((('Z) y z (_ _) pf)
                  (LEZ z))
                ((('S x) ('S y) ('S z) (_ _ _ xLEy) (_ _ _ yLEz))
                  (((LES x) z) (((((leTrans x) y) z) xLEy) yLEz))))))))))
    (leS (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((('Z) y (_ _))
              (LEZ (S y)))
            ((('S x) ('S y) (_ _ _ xLEy))
              (((LES x) (S y)) (((leS x) y) xLEy))))))))
    (lemmaLTZ 'CannotBeCalled)
    (wfLT (lambda (x)
      (letrec* ((f (lambda (_e0)
        (lambda (_e1)
          (lambda (_e2)
            (match (list _e0 _e1 _e2)
              ((('Z) y pf)
                (((lemmaLTZ (((Acc Nat) LT) y)) y) pf))
              ((('S x) y (_ _ _ yLEx))
                ((((MkAcc Nat) LT) y) (lambda (z)
                  (lambda (zLTy)
                    (((f x) z) (((((leTrans (S z)) y) x) zLTy) yLEx))))))))))))
        ((((MkAcc Nat) LT) x) (f x)))))
    (length (lambda (_e0)
      (match (list _e0)
        ((('Nil))
          Z)
        ((('Cons x xs))
          (S (length xs))))))
    (Shorter (lambda (xs)
      (lambda (ys)
        ((LT (length xs)) (length ys)))))
    (wfShorter (lambda (xs)
      (letrec* ((f (lambda (_e0)
        (lambda (_e1)
          (lambda (_e2)
            (match (list _e0 _e1 _e2)
              ((('Nil) ys pf)
                (((lemmaLTZ (((Acc NList) Shorter) ys)) (length ys)) pf))
              ((('Cons x xs) ys (_ _ _ yLEx))
                ((((MkAcc NList) Shorter) ys) (lambda (zs)
                  (lambda (zLTy)
                    (((f xs) zs) (((((leTrans (S (length zs))) (length ys)) (length xs)) zLTy) yLEx))))))))))))
        ((((MkAcc NList) Shorter) xs) (f xs)))))
    (leq (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((('Z) y)
            True)
          ((('S x) ('Z))
            False)
          ((('S x) ('S y))
            ((leq x) y))))))
    (not_TT (lambda (_e0)
      (match (list _e0)
        ((('True))
          False)
        ((('False))
          True))))
    (qel (lambda (y)
      (lambda (x)
        ((leq x) y))))
    (gt (lambda (x)
      (lambda (y)
        (not_TT ((leq y) x)))))
    (condCons (lambda (_e0)
      (match (list _e0)
        ((('True))
          Cons)
        ((('False))
          (lambda (x)
            (lambda (xs)
              xs))))))
    (filter (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((p ('Nil))
            Nil)
          ((p ('Cons x xs))
            (((condCons (p x)) x) ((filter p) xs)))))))
    (append_TT (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((('Nil) ys)
            ys)
          ((('Cons x xs) ys)
            ((Cons x) ((append_TT xs) ys)))))))
    (Id (lambda (a)
      (lambda (_x23)
        (lambda (_x24)
          `(Id ,a ,_x23 ,_x24)))))
    (Refl (lambda (a)
      (lambda (x)
        `(Refl ,a ,x))))
    (Split (lambda (_x25)
      `(Split ,_x25)))
    (SNil `(SNil))
    (SOne (lambda (x)
      `(SOne ,x)))
    (SMore (lambda (x)
      (lambda (xs)
        (lambda (y)
          (lambda (ys)
            `(SMore ,x ,xs ,y ,ys))))))
    (pushL (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((x _ ('SNil))
              (SOne x))
            ((x _ ('SOne y))
              ((((SMore x) Nil) y) Nil))
            ((x _ ('SMore y ys z zs))
              ((((SMore x) ((Cons y) ys)) z) zs)))))))
    (split (lambda (_e0)
      (match (list _e0)
        ((('Nil))
          SNil)
        ((('Cons x ('Nil)))
          (SOne x))
        ((('Cons x ('Cons y xs)))
          (letrec* ((step (lambda (_e0)
            (lambda (_e1)
              (lambda (_e2)
                (lambda (_e3)
                  (match (list _e0 _e1 _e2 _e3)
                    ((('Z) x y xs)
                      ((((SMore x) Nil) y) xs))
                    ((('S ('Z)) x y xs)
                      ((((SMore x) Nil) y) xs))
                    ((('S ('S c)) x y ('Nil))
                      ((((SMore x) Nil) y) Nil))
                    ((('S ('S c)) x y ('Cons z xs))
                      (((pushL x) ((Cons y) ((Cons z) xs))) ((((step c) y) z) xs))))))))))
            ((((step (S (length xs))) x) y) xs))))))
    (merge (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((('Nil) ys)
            ys)
          ((xs ('Nil))
            xs)
          ((('Cons x xs) ('Cons y ys))
            (letrec* ((f (lambda (_e0)
              (match (list _e0)
                ((('True))
                  ((Cons x) ((merge xs) ((Cons y) ys))))
                ((('False))
                  ((Cons y) ((merge ((Cons x) xs)) ys)))))))
              (f ((leq x) y))))))))
    (QSortAcc (lambda (_x0)
      `(QSortAcc ,_x0)))
    (QNil `(QNil))
    (QCons (lambda (x)
      (lambda (xs)
        (lambda (_x1)
          (lambda (_x2)
            `(QCons ,x ,xs ,_x1 ,_x2))))))
    (flemma (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((x p ('Nil))
              (((LES Z) Z) (LEZ Z)))
            ((x p ('Cons y ys))
              (letrec* ((f (lambda (_e0)
                (match (list _e0)
                  ((('True))
                    (((LES (S (length ((filter p) ys)))) (S (length ys))) (((flemma x) p) ys)))
                  ((('False))
                    (((leS (S (length ((filter p) ys)))) (S (length ys))) (((flemma x) p) ys)))))))
                (f (p y)))))))))
    (qsortAcc (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((('Nil) acc)
            QNil)
          ((('Cons x xs) (_ _ _ _ acc))
            ((((QCons x) xs) ((qsortAcc ((filter (qel x)) xs)) ((acc ((filter (qel x)) xs)) (((flemma x) (qel x)) xs)))) ((qsortAcc ((filter (gt x)) xs)) ((acc ((filter (gt x)) xs)) (((flemma x) (gt x)) xs)))))))))
    (qsort_ (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((('Nil) _)
            Nil)
          ((('Cons x xs) (_ _ _ lo hi))
            ((append_TT ((qsort_ ((filter (qel x)) xs)) lo)) ((Cons x) ((qsort_ ((filter (gt x)) xs)) hi))))))))
    (qsort (lambda (xs)
      ((qsort_ xs) ((qsortAcc xs) (wfShorter xs)))))
    (main (qsort someList))
  )
    main))