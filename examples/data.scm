(define Z
  (list 'Z))

(define S
  (lambda (e0)
    (list 'S e0)))

(define plus
  (lambda (m)
    (lambda (n)
      (case (car m)
        ((Z) n)
        ((S) (let* ((_args-m_ (cdr m)) (m_ (car _args-m_)))
          (S ((plus m_) n))))))))

(define main
  (let ((pred (lambda (x)
    (case (car x)
      ((Z) Z)
      ((S) (let* ((_args-x_ (cdr x)) (x_ (car _args-x_)))
        x_))))))
    ((plus (pred (S (S (S (S Z)))))) (pred (S (S (S (S (S Z)))))))))

(print main)
