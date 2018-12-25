(import (chicken process-context))
(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (T `(T))
    (F `(F))
    (MkUnit `(MkUnit))
    (not_TT (lambda (_e0)
      (match (list _e0)
        ((('T))
          F)
        ((('F))
          T))))
    (main (not_TT (letrec* ((f (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((('F) ('MkUnit))
            MkUnit)
          ((('T) ('T))
            F)
          ((('T) ('F))
            T))))))
      ((f (not_TT F)) T))))
  )
    main))
