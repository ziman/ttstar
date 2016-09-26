(define Z
  (list 'Z))

(define S
  (lambda (x)
    (list 'S x)))

(define Nil
  (list 'Nil))

(define Cons
  (lambda (n)
    (lambda (xs)
      (list 'Cons n xs))))

(define vlen
  (lambda (n)
    (lambda (xs)
      (case (car xs)
        ((Nil) n)
        ((Cons) (let* ((_args-m (cdr xs)) (m (car _args-m)))
          (let* ((_args-ys (cdr _args-m)) (ys (car _args-ys)))
            (S ((vlen m) ys)))))))))

(define main
  ((vlen (S Z)) ((Cons Z) Nil)))

main
