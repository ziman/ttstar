(require-extension matchable)
(define Type #(Type))
(define (number->peano z s i) (if (= i 0) (vector z) (vector s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (Void (vector 'Void))
    (Maybe (lambda (_x0)
      (vector 'Maybe _x0)))
    (Just (lambda (a)
      (lambda (x)
        (vector 'Just a x))))
    (Nothing (lambda (a)
      (vector 'Nothing a)))
    (Bool (vector 'Bool))
    (True (vector 'True))
    (False (vector 'False))
    (retTy (lambda (_e0)
      (match (list _e0)
        ((#('Just _ t))
          Bool)
        ((#('Nothing _))
          Type))))
    (f (lambda (_e0)
      (match (list _e0)
        ((#('Just _ b))
          b)
        ((#('Nothing _))
          Bool))))
    (main (f ((Just Bool) False)))
  )
    main))
