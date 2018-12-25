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
    (T `(T))
    (F `(F))
    (Cons (curried-lambda (e0 e1)
      `(Cons ,e0 ,e1)))
    (Nil `(Nil))
    (Nothing `(Nothing))
    (Just `(Just))
    (not_TT (lambda (_pv0)
      (rts-case _pv0
        ((F) T)
        ((T) F))))
    (RNil `(RNil))
    (RSnoc (curried-lambda (e0 e1)
      `(RSnoc ,e0 ,e1)))
    (rev_ (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((Cons _pv2 _pv3) ((rev_ ((RSnoc _pv2) _pv0)) _pv3))
        ((Nil) _pv0))))
    (rev (lambda (xs)
      ((rev_ RNil) xs)))
    (reverse_ (lambda (_pv0)
      (rts-case _pv0
        ((RNil) Nil)
        ((RSnoc _pv1 _pv2) ((Cons _pv1) (reverse_ _pv2))))))
    (reverse_TT (lambda (xs)
      (reverse_ (rev xs))))
    (VNil `(VNil))
    (VOne `(VOne))
    (VTwo (curried-lambda (e0 e1 e2)
      `(VTwo ,e0 ,e1 ,e2)))
    (length (lambda (_pv0)
      (rts-case _pv0
        ((Cons _pv1 _pv2) (S (length _pv2)))
        ((Nil) Z))))
    (build (curried-lambda (_pv0 _pv1 _pv2)
      (rts-case _pv0
        ((S _pv3) (rts-case _pv3
          ((S _pv4) (rts-case _pv1
            ((Cons _pv5 _pv6) (rts-case _pv2
              ((Cons _pv7 _pv8) (((VTwo _pv5) (((build _pv4) _pv6) _pv8)) _pv7))
              (_ VNil)))
            (_ VNil)))
          ((Z) (rts-case _pv1
            ((Cons _pv4 _pv5) (rts-case _pv2
              ((Cons _pv6 _pv7) VOne)
              (_ VNil)))
            (_ VNil)))
          (_ VNil)))
        ((Z) VNil))))
    (toV (lambda (xs)
      (((build (length xs)) xs) (reverse_TT xs))))
    (decEq (curried-lambda (_pv0 _pv1)
      (rts-case _pv0
        ((F) (rts-case _pv1
          ((F) Just)
          ((T) Nothing)))
        ((T) (rts-case _pv1
          ((F) Nothing)
          ((T) Just))))))
    (isPalinV (lambda (_pv0)
      (rts-case _pv0
        ((VNil) Just)
        ((VOne) Just)
        ((VTwo _pv1 _pv2 _pv3) 
          (letrec ((isPalinV_ (curried-lambda (_pv4 _pv5)
            (rts-case _pv4
              ((Just) (rts-case _pv5
                ((Just) Just)
                (_ Nothing)))
              (_ Nothing)))))
            ((isPalinV_ ((decEq _pv1) _pv3)) (isPalinV _pv2)))))))
    (isPalindrome (lambda (xs)
      (isPalinV (toV xs))))
    (genList (curried-lambda (_pv0 _pv1)
      (rts-case _pv1
        ((S _pv2) ((Cons _pv0) ((genList (not_TT _pv0)) _pv2)))
        ((Z) Nil))))
    (isJust (lambda (_pv0)
      (rts-case _pv0
        ((Just) T)
        ((Nothing) F))))
    (main 
      (letrec* (
        (inputSize (rts-arg-peano 'Z 'S 0))
        (inputList ((genList T) inputSize))
      ) (isJust (isPalindrome inputList))))
  ) main))
(newline)
