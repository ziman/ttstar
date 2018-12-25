(import (chicken process-context))
(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (TyEq (lambda (_x0)
      (lambda (_x1)
        `(TyEq ,_x0 ,_x1))))
    (Refl (lambda (a)
      `(Refl ,a)))
    (coerce (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((a _ (_ _))
              (lambda (x)
                x)))))))
    (sym (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((a _ (_ _))
              (Refl a)))))))
    (loopy (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((a b pf)
              (letrec* ((w (lambda (x)
                (((((coerce a) '_) pf) x) x))))
                (w ((((coerce '_) a) (((sym a) '_) pf)) w)))))))))
    (main Type)
  )
    main))
