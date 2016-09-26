(define Q
  (list 'Q))

(define W
  (list 'W))

(define T
  (list 'T))

(define F
  (list 'F))

(define not
  (lambda (x)
    (case (car x)
      ((T) F)
      ((F) T))))

(define mot
  (lambda (m)
    (case (car m)
      ((Q) W)
      ((W) Q))))

(define invert
  (lambda (t)
    (lambda (x)
      (case (car t)
        ((T) (not x))
        ((F) (mot x))))))

(define main
  ((invert F) Q))

main
