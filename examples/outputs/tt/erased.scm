(import (chicken process-context))
(require-extension matchable)
(define Type '(Type))
(define (number->peano z s i) (if (= i 0) (list z) (list s (number->peano z s (- i 1)))))
(define (rts-arg-peano z s i) (number->peano z s (string->number (list-ref (command-line-arguments) i))))
(define (rts-arg-read i) (read (open-input-string (list-ref (command-line-arguments) i))))
(print
  (letrec* (
    (FZ `(FZ))
    (FS (lambda (_x16)
      `(FS ,_x16)))
    (VN `(VN))
    (VC (lambda (x)
      (lambda (xs)
        `(VC ,x ,xs))))
    (V (lambda (_x1)
      `(V ,_x1)))
    (Lam (lambda (_x2)
      `(Lam ,_x2)))
    (App (lambda (_x3)
      (lambda (_x4)
        `(App ,_x3 ,_x4))))
    (env (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((('VC x xs) ('FZ))
            x)
          ((('VC x xs) ('FS i))
            ((env xs) i))))))
    (extendMap (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((f ('FZ))
            FZ)
          ((f ('FS i))
            (FS (f i)))))))
    (mapVars (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((f ('V i))
            (V (f i)))
          ((f ('Lam x))
            (Lam ((mapVars (extendMap f)) x)))
          ((f ('App g x))
            ((App ((mapVars f) g)) ((mapVars f) x)))))))
    (extendSubst (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((f ('FZ))
            (V FZ))
          ((f ('FS i))
            ((mapVars FS) (f i)))))))
    (substVars (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((f ('V i))
            (f i))
          ((f ('Lam x))
            (Lam ((substVars (extendSubst f)) x)))
          ((f ('App g x))
            ((App ((substVars f) g)) ((substVars f) x)))))))
    (testTm ((App (Lam ((App (V FZ)) (V (FS FZ))))) (Lam ((App (V (FS FZ))) (V FZ)))))
    (example1 ((substVars (env ((VC (Lam (V FZ))) VN))) testTm))
    (substTop (lambda (_e0)
      (lambda (_e1)
        (match (list _e0 _e1)
          ((tm ('FZ))
            tm)
          ((tm ('FS i))
            (V i))))))
    (nf (lambda (_e0)
      (match (list _e0)
        ((('V i))
          (V i))
        ((('Lam x))
          (Lam (nf x)))
        ((('App f x))
          (letrec* ((g (lambda (_e0)
            (match (list _e0)
              ((('Lam y))
                (nf ((substVars (substTop (nf x))) y)))
              ((f_)
                ((App f_) (nf x)))))))
            (g (nf f)))))))
    (example2 (nf testTm))
    (R (lambda (x)
      (lambda (y)
        `(R ,x ,y))))
    (main ((R example1) example2))
  )
    main))
