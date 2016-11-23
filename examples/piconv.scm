(define A
  (list 'A))

(define const_A
  A)

(define apply_TT
  (lambda (f)
    f))

(define main
  (apply_TT const_A))

(print main)
