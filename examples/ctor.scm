(define T
  (list 'T))

(define MkUnit
  (list 'MkUnit))

(define not_TT
  (lambda (x)
    (case (car x)
      ((T) MkUnit))))

(define main
  (not_TT T))

(print main)
