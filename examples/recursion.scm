(define Z
  (list 'Z))

(define S
  (lambda (n)
    (list 'S n)))

(define VNil
  (list 'VNil))

(define VCons
  (lambda (xs)
    (list 'VCons xs)))

(define vlen
  (lambda (xs)
    (case (car xs)
      ((VNil) Z)
      ((VCons) (let* ((_args-xs_ (cdr xs)) (xs_ (car _args-xs_)))
        (S (vlen xs_)))))))

(define testVec
  (VCons (VCons VNil)))

(define main
  (vlen testVec))

(print main)(newline)
