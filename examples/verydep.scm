(define Just
  (lambda (x)
    (list 'Just x)))

(define Bool
  (list 'Bool))

(define False
  (list 'False))

(define f
  (lambda (x)
    (case (car x)
      ((Just) (let* ((_args-b (cdr x)) (b (car _args-b)))
        b)))))

(define main
  (f (Just False)))

(print main)
