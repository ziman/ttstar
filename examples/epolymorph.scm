(define Z
  (list 'Z))

(define S
  (lambda (n)
    (list 'S n)))

(define Plus
  (lambda (x)
    (lambda (y)
      (list 'Plus x y))))

(define id
  (lambda (x)
    (case (car x)
      ((Z) Z)
      ((S) (let* ((_args-y (cdr x)) (y (car _args-y)))
        (let ((result (S y)))
          result))))))

(define const_3
  (lambda (_)
    (S (S (S Z)))))

(define two
  (S (S Z)))

(define f
  (lambda (g)
    (lambda (z)
      (lambda (h)
        (lambda (w)
          ((Plus (g z)) (h w)))))))

(define apply
  (lambda (f)
    (lambda (x)
      (f x))))

(define test_1
  ((Plus ((apply id) (S (S Z)))) ((apply const_3) two)))

(define test_2
  ((((f id) (S (S Z))) const_3) (S Z)))

(define main
  ((Plus test_1) test_2))

main
