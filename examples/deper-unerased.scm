(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (Bool `(Bool))
    (T `(T))
    (F `(F))
    (TwoBools `(TwoBools))
    (TB (lambda (x)
      (lambda (y)
        `(TB ,x ,y))))
    (id (lambda (x)
      x))
    (constT (lambda (_0)
      T))
    (fty (lambda (_e0)
      (match (list _e0)
        ((('T))
          '_)
        ((('F))
          '_))))
    (f (lambda (_e0)
      (match (list _e0)
        ((('T))
          id)
        ((('F))
          constT))))
    (main ((TB ((f T) F)) ((f F) F)))
  )
    main))
