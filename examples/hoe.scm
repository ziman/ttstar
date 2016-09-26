(define A
  (list 'A))

(define B
  (list 'B))

(define Op
  (lambda (x)
    (lambda (y)
      (list 'Op x y))))

(define id
  (lambda (x)
    x))

(define const_A
  A)

(define f
  (lambda (g)
    (lambda (z)
      (lambda (h)
        ((Op (g z)) h)))))

(define main
  (((f id) B) const_A))

main
