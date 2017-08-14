(define-syntax curried-lambda
  (syntax-rules ()
    ((curried-lambda () body) body)
    ((curried-lambda (x . xs) body)
      (lambda (x) (curried-lambda xs body)))))

(define-syntax rts-unpack
  (syntax-rules ()
    ((rts-unpack xs () rhs) rhs)
    ((rts-unpack xs (v . vs) rhs)
      (let ((v (car xs)))
        (rts-unpack (cdr xs) vs rhs)))))

(define-syntax rts-case-int
  (syntax-rules (_)
    ((rts-case-int tag args)
     (error "pattern match failure" (list tag args)))
    ((rts-case-int tag args (_ rhs) . rest)
     rhs)
    ((rts-case-int tag args ((_ . pvs) rhs) . rest)
     (rts-unpack args pvs rhs))
    ((rts-case-int tag args ((cn . pvs) rhs) . rest)
     (if (eq? tag 'cn)
         (rts-unpack args pvs rhs)
         (rts-case-int tag args . rest)))))

(define-syntax rts-case
  (syntax-rules ()
    ((rts-case s . alts) (rts-case-int (car s) (cdr s) . alts))))

(define Type '(Type))

(define (number->peano z s i)
  (if (= i 0)
    (list z)
    (list s (number->peano z s (- i 1)))))

(define (rts-arg-peano z s i)
  (number->peano z s (string->number
                       (list-ref (command-line-arguments) i))))

(define (rts-arg-read i)
  (read (open-input-string
          (list-ref (command-line-arguments) i))))

(display
  (letrec* (
    (True `(True))
    (False `(False))
    (Z `(Z))
    (S (lambda (e0)
      `(S ,e0)))
    (Even `(Even))
    (Odd `(Odd))
    (fun (lambda (_pv0)
      (rts-case _pv0
        ((Even) (lambda (n)
          (letrec ((f (lambda (_pv1)
            (rts-case _pv1
              ((S _pv2) ((fun Odd) _pv2))
              ((Z) True)))))
            (f n))))
        ((Odd) (lambda (n)
          (letrec ((f (lambda (_pv1)
            (rts-case _pv1
              ((S _pv2) ((fun Even) _pv2))
              ((Z) False)))))
            (f n)))))))
    (even (fun Even))
    (main (even (S (S (S (S (S (S (S (S Z))))))))))
  )
    main))
(newline)
