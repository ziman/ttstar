(define T
  (list 'T))

(define P
  (lambda (e0)
    (list 'P e0)))

(define fst
  (lambda (x)
    (case (car x)
      ((P) (let* ((_args-y (cdr x)) (y (car _args-y)))
        y)))))

(define main
  (fst (P T)))

(print main)
