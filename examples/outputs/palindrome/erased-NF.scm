(import (chicken process-context))
(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (Z `(Z))
    (S (lambda (_x0)
      `(S ,_x0)))
    (T `(T))
    (F `(F))
    (Cons (lambda (_x1)
      (lambda (_x2)
        `(Cons ,_x1 ,_x2))))
    (Nil `(Nil))
    (Nothing `(Nothing))
    (Just `(Just))
    (not_TT (lambda (_e0)
      (match (list _e0)
        ((('T))
          F)
        ((('F))
          T))))
    (RNil `(RNil))
    (RSnoc (lambda (x)
      (lambda (rxs)
        `(RSnoc ,x ,rxs))))
    (rev_ (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((rxs ('Nil))
            rxs)
          ((rxs ('Cons y ys))
            ((rev_ ((RSnoc y) rxs)) ys))))))
    (reverse_ (lambda (_e0)
      (match (list _e0)
        ((('RNil))
          Nil)
        ((('RSnoc x rxs))
          ((Cons x) (reverse_ rxs))))))
    (VNil `(VNil))
    (VOne `(VOne))
    (VTwo (lambda (x)
      (lambda (u)
        (lambda (y)
          `(VTwo ,x ,u ,y)))))
    (length (lambda (_e0)
      (match (list _e0)
        ((('Nil))
          Z)
        ((('Cons x xs))
          (S (length xs))))))
    (build (lambda (_e0)
      (lambda (_e1)
        (lambda (_e2)
          (match (list _e0 _e1 _e2)
            ((('Z) xs ys)
              VNil)
            ((('S ('Z)) ('Cons x xs) ('Cons y ys))
              VOne)
            ((('S ('S n)) ('Cons x xs) ('Cons y ys))
              (((VTwo x) (((build n) xs) ys)) y))
            ((('S n) ('Nil) ('Nil))
              VNil))))))
    (decEq (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((('T) ('T))
            Just)
          ((('F) ('F))
            Just)
          ((('T) ('F))
            Nothing)
          ((('F) ('T))
            Nothing)))))
    (isPalinV (lambda (_e0)
      (match (list _e0)
        ((('VNil))
          Just)
        ((('VOne))
          Just)
        ((('VTwo x v y))
          (letrec* ((isPalinV_ (lambda (_e0)
            (lambda (_e1)
              (match (list _e0 _e1)
                ((('Just) ('Just))
                  Just)
                ((pfB pfV)
                  Nothing))))))
            ((isPalinV_ ((decEq x) y)) (isPalinV v)))))))
    (genList (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((b ('Z))
            Nil)
          ((b ('S n))
            ((Cons b) ((genList (not_TT b)) n)))))))
    (isJust (lambda (_e0)
      (match (list _e0)
        ((('Just))
          T)
        ((('Nothing))
          F))))
  )
    (letrec* ((inputSize (rts-arg-peano 'Z 'S 0)))
      (isJust (isPalinV (((build (length ((genList T) inputSize))) ((genList T) inputSize)) (reverse_ ((rev_ RNil) ((genList T) inputSize)))))))))
