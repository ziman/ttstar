(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
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
                ((a P x _ _)
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
    (Bool `(Bool))
    (T `(T))
    (F `(F))
    (List `(List))
    (Nil `(Nil))
    (Cons (lambda (x)
      (lambda (xs)
        `(Cons ,x ,xs))))
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
    (Rev (lambda (_x7)
      `(Rev ,_x7)))
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
    (main (reverse_TT ((Cons T) ((Cons F) ((Cons T) ((Cons F) Nil))))))
  )
    main))