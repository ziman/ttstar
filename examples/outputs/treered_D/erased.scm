(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (True `(True))
    (False `(False))
    (Yeah `(Yeah))
    (Nope `(Nope))
    (Nothing `(Nothing))
    (Just (lambda (x)
      `(Just ,x)))
    (g (lambda (_e0)
      (match (list _e0)
        ((('Just ('True)))
          Yeah)
        ((('Just ('False)))
          Nope)
        ((('Nothing))
          Nope))))
    (main (g (Just True)))
  )
    main))