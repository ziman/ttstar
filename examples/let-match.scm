(define T
  (list 'T))

(define F
  (list 'F))

(define main
  ((let ((not_TT (lambda (x)
    (case (car x)
      ((T) F)
      ((F) T)))))
    not_TT) F))

(print main)
