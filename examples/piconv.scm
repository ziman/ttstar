(define A
  (list 'A))

(define const_A
  A)

(define apply
  (lambda (f)
    f))

(define main
  (apply const_A))

(print main)(newline)
