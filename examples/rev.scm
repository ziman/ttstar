(define subst
  (lambda (w)
    w))

(define T
  (list 'T))

(define F
  (list 'F))

(define Nil
  (list 'Nil))

(define Cons
  (lambda (x)
    (lambda (xs)
      (list 'Cons x xs))))

(define RNil
  (list 'RNil))

(define RSnoc
  (lambda (x)
    (lambda (rxs)
      (list 'RSnoc x rxs))))

(define rev_
  (lambda (rxs)
    (lambda (ys)
      (case (car ys)
        ((Nil) (subst rxs))
        ((Cons) (let* ((_args-y (cdr ys)) (y (car _args-y)))
          (let* ((_args-ys_ (cdr _args-y)) (ys_ (car _args-ys_)))
            (subst ((rev_ ((RSnoc y) rxs)) ys_)))))))))

(define rev
  (lambda (xs)
    ((rev_ RNil) xs)))

(define reverse_
  (lambda (rxs)
    (case (car rxs)
      ((RNil) Nil)
      ((RSnoc) (let* ((_args-x (cdr rxs)) (x (car _args-x)))
        (let* ((_args-rxs_ (cdr _args-x)) (rxs_ (car _args-rxs_)))
          ((Cons x) (reverse_ rxs_))))))))

(define reverse
  (lambda (xs)
    (reverse_ (rev xs))))

(define main
  (reverse ((Cons T) ((Cons F) ((Cons T) ((Cons F) Nil))))))

main
