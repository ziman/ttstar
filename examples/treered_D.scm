(define True
  (list 'True))

(define Yeah
  (list 'Yeah))

(define Nope
  (list 'Nope))

(define Just
  (lambda (x)
    (list 'Just x)))

(define g
  (lambda (x)
    (case (car x)
      ((Just) (let* ((_args-b (cdr x)) (b (car _args-b)))
        (case (car b)
          ((True) Yeah)))))))

(define main
  (g (Just True)))

(print main)
