(define T
  (list 'T))

(define F
  (list 'F))

(define not_TT
  (lambda (x)
    (case (car x)
      ((T) F)
      ((F) T))))

(define main
  not_TT)

(print main)
