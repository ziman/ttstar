(require-extension matchable)
(define Type #(Type))
(define (number->peano z s i) (if (= i 0) (vector z) (vector s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (True (vector 'True))
    (False (vector 'False))
    (Yeah (vector 'Yeah))
    (Nope (vector 'Nope))
    (Nothing (vector 'Nothing))
    (Just (lambda (x)
      (vector 'Just x)))
    (g (lambda (_e0)
      (match (list _e0)
        ((#('Just #('True)))
          Yeah)
        ((#('Just #('False)))
          Nope)
        ((#('Nothing))
          Nope))))
    (main (g (Just True)))
  )
    main))
