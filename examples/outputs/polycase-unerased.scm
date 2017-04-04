(require-extension matchable)
(define Type #(Type))
(define (number->peano z s i) (if (= i 0) (vector z) (vector s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (Mool (vector 'Mool))
    (Q (vector 'Q))
    (W (vector 'W))
    (Bool (vector 'Bool))
    (T (vector 'T))
    (F (vector 'F))
    (Id (lambda (a)
      (lambda (x)
        (lambda (y)
          (vector 'Id a x y)))))
    (Refl (lambda (a)
      (lambda (x)
        (vector 'Refl a x))))
    (not_TT (lambda (_e0)
      (match (list _e0)
        ((#('T))
          F)
        ((#('F))
          T))))
    (notnot (lambda (_e0)
      (match (list _e0)
        ((#('T))
          ((Refl Bool) T))
        ((#('F))
          ((Refl Bool) F)))))
    (retTy (lambda (_e0)
      (match (list _e0)
        ((#('T))
          Bool)
        ((#('F))
          Mool))))
    (mot (lambda (_e0)
      (match (list _e0)
        ((#('Q))
          W)
        ((#('W))
          Q))))
    (invert (lambda (_e0)
      (match (list _e0)
        ((#('T))
          not_TT)
        ((#('F))
          mot))))
    (invert_ (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((#('T) x)
            (not_TT x))
          ((#('F) x)
            (mot x))))))
    (main ((invert F) Q))
  )
    main))
