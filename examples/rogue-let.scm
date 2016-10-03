(define T
  (list 'T))

(define F
  (list 'F))

(define not
  (lambda (x)
    (case (car x)
      ((T) F)
      ((F) T))))

(define main
  not)

(print main)(newline)
