(require-extension matchable)
(define Type #(Type))
(define (number->peano z s i) (if (= i 0) (vector z) (vector s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (Bool (vector 'Bool))
    (T (vector 'T))
    (F (vector 'F))
    (not_TT (lambda (_e0)
      (match (list _e0)
        ((#('T))
          F)
        ((#('F))
          T))))
    (main not_TT)
  )
    main))
