(define A
  (list 'A))

(define B
  (list 'B))

(define Op
  (lambda (x)
    (lambda (y)
      (list 'Op x y))))

(define id
  (lambda (y)
    y))

(define constA
  A)

(define apply_REE
  (lambda (f)
    f))

(define apply_RRR
  (lambda (f)
    (lambda (x)
      (f x))))

(define test1
  ((apply_RRR id) B))

(define test2
  (apply_REE constA))

(define main
  ((Op test1) test2))

(print main)(newline)
