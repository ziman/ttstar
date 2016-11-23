(define T
  (list 'T))

(define F
  (list 'F))

(define TB
  (lambda (x)
    (lambda (y)
      (list 'TB x y))))

(define id
  (lambda (x)
    x))

(define constT
  T)

(define f
  (lambda (x)
    (case (car x)
      ((T) id)
      ((F) constT))))

(define main
  ((TB ((f T) F)) (f F)))

(print main)
