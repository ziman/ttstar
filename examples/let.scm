(define Z
  (list 'Z))

(define S
  (lambda (_)
    (list 'S _)))

(define plus
  (lambda (n)
    (lambda (m)
      (case (car n)
        ((Z) m)
        ((S) (let* ((_args-n_ (cdr n)) (n_ (car _args-n_)))
          (S ((plus n_) m))))))))

(define id
  (lambda (x)
    x))

(define const
  (lambda (x)
    (lambda (y)
      x)))

(define main
  (let ((apply (lambda (f)
    (lambda (x)
      (case (car x)
        ((Z) (f Z))
        ((S) (let* ((_args-x_ (cdr x)) (x_ (car _args-x_)))
          (f (S x_)))))))))
    (let ((Q (list 'Q)))
      (let ((three (S (S (S Z)))))
        ((plus ((apply id) (S (S Z)))) ((apply (const Q)) three))))))

(print main)(newline)
