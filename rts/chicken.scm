(require-extension matchable)

; usage:
; (curried-lambda (x y z) (f x y z))
(define-syntax curried-lambda
  (syntax-rules ()
    [(curried-lambda () body) body]
    [(curried-lambda (x . xs) body)
      (lambda (x) (curried-lambda xs body))]))

; usage:
; (define MkPair (constructor MkPair x y))
(define-syntax constructor
  (syntax-rules ()
    [(constructor n . args)
        (curried-lambda args (list 'n . args))]))
