(define Z
  (list 'Z))

(define S
  (lambda (x)
    (list 'S x)))

(define Nil
  (list 'Nil))

(define Cons
  (lambda (x)
    (lambda (xs)
      (list 'Cons x xs))))

(define append_TT
  (lambda (xs)
    (lambda (ys)
      (case (car xs)
        ((Nil) ys)
        ((Cons) (let* ((_args-x (cdr xs)) (x (car _args-x)))
          (let* ((_args-xs_ (cdr _args-x)) (xs_ (car _args-xs_)))
            ((Cons x) ((append_TT xs_) ys)))))))))

(define main
  ((append_TT Nil) ((Cons (S (S (S (S Z))))) Nil)))

(print main)
