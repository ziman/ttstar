(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (T `(T))
    (F `(F))
    (P (lambda (x)
      (lambda (y)
        `(P ,x ,y))))
    (fst (lambda (_e0)
      (match (list _e0)
        ((('P l _))
          l))))
    (snd (lambda (_e0)
      (match (list _e0)
        ((('P _ r))
          r))))
    (and (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((('T) y)
            y)
          ((('F) _)
            F)))))
    (main ((and (fst ((P T) F))) (snd ((P F) T))))
  )
    main))
