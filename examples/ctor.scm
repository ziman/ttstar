(define T
  (list 'T))

(define MkUnit
  (list 'MkUnit))

(define not
  (lambda (x)
    (case (car x)
      ((T) MkUnit))))

(define main
  (not T))

(print main)(newline)
