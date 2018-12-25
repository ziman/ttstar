(import (chicken process-context))

(define-syntax curried-lambda
  (syntax-rules ()
    ((curried-lambda () body) body)
    ((curried-lambda (x . xs) body)
      (lambda (x) (curried-lambda xs body)))))

(define-syntax rts-unpack
  (syntax-rules ()
    ((rts-unpack xs () rhs) rhs)
    ((rts-unpack xs (v . vs) rhs)
      (let ((v (car xs)) (rest (cdr xs)))
        (rts-unpack rest vs rhs)))))

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
    (Z `(Z))
    (S (lambda (e0)
      `(S ,e0)))
    (True `(True))
    (False `(False))
    (Nil `(Nil))
    (Cons (curried-lambda (e0 e1)
      `(Cons ,e0 ,e1)))
    (repl (curried-lambda (_pv0 _pv1 _pv2)
      (rts-case _pv0
        ((S _pv3) ((Cons _pv1) (((repl _pv3) _pv1) _pv2)))
        ((Z) _pv2))))
    (RNil `(RNil))
    (RCons (curried-lambda (e0 e1 e2)
      `(RCons ,e0 ,e1 ,e2)))
    (compress (lambda (_pv0)
      (rts-case _pv0
        ((Cons _pv1 _pv2) 
          (letrec ((aux (curried-lambda (_pv3 _pv4)
            (rts-case _pv4
              ((RNil) (((RCons (S Z)) _pv3) RNil))
              (_ (rts-case _pv3
                ((False) (rts-case _pv4
                  ((RCons _pv5 _pv6 _pv7) (rts-case _pv6
                    ((False) (((RCons (S _pv5)) False) _pv7))
                    ((True) (((RCons (S Z)) False) (((RCons _pv5) True) _pv7)))))))
                ((True) (rts-case _pv4
                  ((RCons _pv5 _pv6 _pv7) (rts-case _pv6
                    ((False) (((RCons (S Z)) True) (((RCons _pv5) False) _pv7)))
                    ((True) (((RCons (S _pv5)) True) _pv7))))))))))))
            ((aux _pv1) (compress _pv2))))
        ((Nil) RNil))))
    (decompress (lambda (_pv0)
      (rts-case _pv0
        ((RCons _pv1 _pv2 _pv3) (((repl _pv1) _pv2) (decompress _pv3)))
        ((RNil) Nil))))
    (foldl (curried-lambda (_pv0 _pv1 _pv2)
      (rts-case _pv2
        ((Cons _pv3 _pv4) (((foldl _pv0) ((_pv0 _pv1) _pv3)) _pv4))
        ((Nil) _pv1))))
    (xor (curried-lambda (_pv0 _pv1)
      (rts-case _pv0
        ((False) _pv1)
        ((True) (rts-case _pv1
          ((False) True)
          ((True) False))))))
    (xors ((foldl xor) False))
    (genInputList (lambda (n)
      (((repl n) True) Nil)))
    (main 
      (letrec* (
        (inputSize (rts-arg-peano 'Z 'S 0))
        (inputList (genInputList inputSize))
      ) (xors (decompress (compress inputList)))))
  ) main))
(newline)
