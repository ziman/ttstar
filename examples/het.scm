(define Tuple
  (lambda (x)
    (lambda (y)
      (lambda (z)
        (lambda (w)
          (list 'Tuple x y z w))))))

(define Bool
  (list 'Bool))

(define T
  (list 'T))

(define F
  (list 'F))

(define Mool
  (list 'Mool))

(define Q
  (list 'Q))

(define W
  (list 'W))

(define f
  (lambda (x)
    (case (car x)
      ((T) Bool)
      ((F) Bool)
      ((Q) Mool)
      ((W) Mool))))

(define main
  ((((Tuple (f T)) (f F)) (f Q)) (f W)))

(print main)
