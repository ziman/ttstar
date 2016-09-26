(define F
  (list 'F))

(define Refl
  (list 'Refl))

(define notnot
  (lambda (x)
    (case (car x)
      ((F) Refl))))

(define main
  (notnot F))

main
