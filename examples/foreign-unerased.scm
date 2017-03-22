(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (N `(N))
    (Z `(Z))
    (S (lambda (x)
      `(S ,x)))
    (B `(B))
    (T `(T))
    (F `(F))
    (List `(List))
    (Cons (lambda (_x0)
      (lambda (_x1)
        `(Cons ,_x0 ,_x1))))
    (Nil `(Nil))
    (not_TT (lambda (_e0)
      (match (list _e0)
        ((('T))
          F)
        ((('F))
          T))))
    (input (rts-arg-peano 'Z 'S 0))
    (genList (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((b ('Z))
            Nil)
          ((b ('S n))
            ((Cons b) ((genList (not_TT b)) n)))))))
    (Eq (lambda (a)
      (lambda (_x5)
        (lambda (_x6)
          `(Eq ,a ,_x5 ,_x6)))))
    (Refl (lambda (a)
      (lambda (x)
        `(Refl ,a ,x))))
    (Maybe (lambda (_x7)
      `(Maybe ,_x7)))
    (Nothing (lambda (a)
      `(Nothing ,a)))
    (Just (lambda (a)
      (lambda (_x8)
        `(Just ,a ,_x8))))
    (semiDecEqB (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((('T) ('T))
            ((Just (((Eq B) T) T)) ((Refl B) T)))
          ((('F) ('F))
            ((Just (((Eq B) F) F)) ((Refl B) F)))
          ((('T) ('F))
            (Nothing (((Eq B) T) F)))
          ((('F) ('T))
            (Nothing (((Eq B) F) T)))))))
    (semiDecEq (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((('Nil) ('Cons b ys))
            (Nothing (((Eq List) Nil) ((Cons b) ys))))
          ((('Cons b xs) ('Nil))
            (Nothing (((Eq List) ((Cons b) xs)) Nil)))
          ((('Nil) ('Nil))
            ((Just (((Eq List) Nil) Nil)) ((Refl List) Nil)))
          ((('Cons x xs) ('Cons y ys))
            (letrec* ((semiDecEq_ (lambda (_e0)
              (lambda (_e1)
                (lambda (_e2)
                  (lambda (_e3)
                    (lambda (_e4)
                      (lambda (_e5)
                        (match (list _e0 _e1 _e2 _e3 _e4 _e5)
                          ((x y xs ys ('Nothing _) pfT)
                            (Nothing (((Eq List) ((Cons x) xs)) ((Cons y) ys))))
                          ((x y xs ys pfH ('Nothing _))
                            (Nothing (((Eq List) ((Cons x) xs)) ((Cons y) ys))))
                          ((x _ xs _ ('Just _ _) ('Just _ _))
                            ((Just (((Eq List) ((Cons x) xs)) ((Cons x) xs))) ((Refl List) ((Cons x) xs)))))))))))))
              ((((((semiDecEq_ x) y) xs) ys) ((semiDecEqB x) y)) ((semiDecEq xs) ys))))))))
    (sampleList ((genList T) input))
    (main (match (list)
      (()
        ((semiDecEq sampleList) sampleList))))
  )
    main))
