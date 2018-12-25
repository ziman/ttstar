(import (chicken process-context))
(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (Mool `(Mool))
    (Q `(Q))
    (W `(W))
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
    (retTy (lambda (_e0)
      (match (list _e0)
        ((('T))
          Bool)
        ((('F))
          Mool))))
    (mot (lambda (_e0)
      (match (list _e0)
        ((('Q))
          W)
        ((('W))
          Q))))
    (invert (lambda (_e0)
      (match (list _e0)
        ((('T))
          not_TT)
        ((('F))
          mot))))
    (invert_ (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((('T) x)
            (not_TT x))
          ((('F) x)
            (mot x))))))
    (main ((invert F) Q))
  )
    main))
