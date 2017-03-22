(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (Bool `(Bool))
    (T `(T))
    (F `(F))
    (Id (lambda (a)
      (lambda (x)
        (lambda (y)
          `(Id ,a ,x ,y)))))
    (Refl (lambda (a)
      (lambda (x)
        `(Refl ,a ,x))))
    (not_TT (lambda (_e0)
      (match (list _e0)
        ((('T))
          F)
        ((('F))
          T))))
    (notnot (lambda (_e0)
      (match (list _e0)
        ((('T))
          ((Refl Bool) T))
        ((('F))
          ((Refl Bool) F)))))
    (subst (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (lambda (_e3)
            (lambda (_e4)
              (match (list _e0 _e1 _e2 _e3 _e4)
                ((a P x _ _)
                  (lambda (w)
                    w)))))))))
    (main (notnot ((((((subst Type) (lambda (a)
      a)) Bool) Bool) ((Refl Type) Bool)) F)))
  )
    main))
