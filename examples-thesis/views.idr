%default total

%hide Prelude.Nat.LT
%hide Prelude.Interfaces.LT
%hide Prelude.Interfaces.(<=)
%hide Prelude.Interfaces.(>)
%hide Prelude.List.filter
%hide Prelude.List.merge
%hide Prelude.List.splitAt
%hide Prelude.WellFounded.Smaller

someList : List Nat
someList = [9,1,5,5,0,2,3,7,6,11,1]

data Acc : (lessThan : a -> a -> Type) -> (x : a) -> Type where
  MkAcc :
    -- potentially infinite tuple
    -- potentially infinite number of children in the tree
    -- but each subtree has a finite depth
    (acc : {y : a} -> (y `lessThan` x) -> Acc lessThan y)
      -> Acc lessThan x

interface WF (lt : a -> a -> Type) where
  wf : (x : _) -> Acc lt x

------------------------------------------

data LE : Nat -> Nat -> Type where
  LEZ : Z `LE` n
  LES : m `LE` n -> S m `LE` S n

LT : Nat -> Nat -> Type
LT m n = LE (S m) n

leRefl : x `LE` x
leRefl {x = Z} = LEZ
leRefl {x = (S x)} = LES leRefl

leTrans : (x `LE` y) -> (y `LE` z) -> (x `LE` z)
leTrans  LEZ _ = LEZ
leTrans (LES xLEy) (LES yLEz) = LES $ leTrans xLEy yLEz

lemmaLTZ : (n `LT` Z) -> a
lemmaLTZ  LEZ    impossible
lemmaLTZ (LES _) impossible

wfLT : (x : Nat) -> Acc LT x
wfLT x = MkAcc (f x)
  where
    f : (x : Nat) -> (y `LT` x) -> Acc LT y
    f  Z     pf        = lemmaLTZ pf
    f (S x) (LES yLEx) = MkAcc (\zLTy => f x $ leTrans zLTy yLEx)

{-
decLE : (m, n : Nat) -> Dec (m `LE` n)
decLE Z n = Yes LEZ
decLE (S k) Z = No lemmaLTZ
decLE (S k) (S j) with (decLE k j)
  | Yes yep = Yes $ LES yep
  | No nope = No $ f nope
    where
      f : (LE k j -> Void) -> LE (S k) (S j) -> Void
      f nope (LES pf) = nope pf
-}

(<=) : Nat -> Nat -> Bool
(<=) Z n = True
(<=) (S m) Z = False
(<=) (S m) (S n) = m <= n

(>) : Nat -> Nat -> Bool
(>) m n = not (m <= n)

filter : (a -> Bool) -> List a -> List a
filter p [] = []
filter p (x :: xs) with (p x)
  | True = x :: filter p xs
  | False = filter p xs

------------------------------------------

shorter : List a -> List a -> Type
shorter xs ys = length xs `LT` length ys

wfShorter : (xs : List a) -> Acc Main.shorter xs
wfShorter xs = MkAcc (f xs)
  where
    f : (xs : List a) -> (ys `Main.shorter` xs) -> Acc Main.shorter ys
    f [] pf = lemmaLTZ pf
    f (x :: xs) (LES ysLExs) = MkAcc (\zsLTys => f xs $ leTrans zsLTys ysLExs)

-----------------------------------------

{- Comes from Prelude now
interface Sized a where
  size : a -> Nat
-}

Smaller : Sized a => a -> a -> Type
Smaller x y = size x `LT` size y

SizeAcc : Sized a => a -> Type
SizeAcc x = Acc Smaller x

wfSmaller : Sized a => (x : a) -> SizeAcc x
wfSmaller x = MkAcc $ f (size x) (wfLT $ size x)
  where
    f : (sizeX : Nat) -> (acc : Acc LT sizeX)
      -> {y : a} -> (size y `LT` sizeX) -> Acc Smaller y
    f Z acc pf = lemmaLTZ pf
    f (S n) (MkAcc acc) (LES yLEx)
      = MkAcc (\zLTy =>
          f n (acc $ LES leRefl) (leTrans zLTy yLEx)
        )

{- comes from Prelude now
implementation Sized (List a) where
  size = length
-}

{-
wfSmaller : Sized a => (x : a) -> Acc Smaller x
wfSmaller x = MkAcc (f x)
  where
    f : (x, y : a) -> (y `Smaller` x) -> Acc Smaller y
    f x y pf with (size x) proof xSize
      f x y pf | Z = lemmaLTZ pf
      f x y (LES yLEx) | S n = MkAcc (\z, zLTy => f x z $ leTrans zLTy ?rhs)
      -- we cannot do this because for the inductive step, we need a subterm of x
      -- but we have no way to obtain it
-}

-----------------------------------------

-- qSort with Acc

leS : (m `LE` n) -> (m `LE` S n)
leS  LEZ    = LEZ
leS (LES x) = LES (leS x)

filterLen : (p : a -> Bool) -> (xs : List a) -> length (filter p xs) `LE` length xs
filterLen p [] = LEZ
filterLen p (x :: xs) with (p x)
  | True = LES $ filterLen p xs
  | False = leS $ filterLen p xs

qsort' : (xs : List Nat) -> (Acc Main.shorter xs) -> List Nat
qsort' [] acc = []
qsort' (x :: xs) (MkAcc acc) =
  qsort' (filter (<= x) xs) (acc $ LES (filterLen (<= x) xs))
  ++ [x]
  ++ qsort' (filter (> x) xs) (acc $ LES (filterLen (> x) xs))

qsort : List Nat -> List Nat
qsort xs = qsort' xs (wfShorter xs)

------------------------

-- QSortAcc directly

data QSortAcc : List Nat -> Type where
  QNil : QSortAcc []
  QCons : QSortAcc (filter (<= x) xs) -> QSortAcc (filter (> x) xs) -> QSortAcc (x :: xs)

qsortAccLo : (x : _) -> QSortAcc xs -> QSortAcc (filter (<= x) xs)
qsortAccLo x pf = ?rhsX1

qsortAccHi : (x : _) -> QSortAcc xs -> QSortAcc (filter (> x) xs)
qsortAccHi x pf = ?rhsX2

qsortA' : (xs : List Nat) -> QSortAcc xs -> List Nat
qsortA' [] QNil = []
qsortA' (x :: xs) (QCons lo hi)
    = qsortA' (filter (<= x) xs) lo
    ++ [x]
    ++ qsortA' (filter (> x) xs) hi

obsBool : (x : Bool) -> Either (x = True) (x = False)
obsBool True = Left Refl
obsBool False = Right Refl

filterDbl : (p : a -> Bool) -> (xs : List a) -> filter p (filter p xs) = filter p xs
filterDbl p xs = ?filterDblHole

qsortAcc : (xs : List Nat) -> QSortAcc xs
qsortAcc [] = QNil
qsortAcc (x :: xs) = QCons (f x xs) ?rhsX3
  where
    f : (x : Nat) -> (xs : List Nat) -> QSortAcc (filter (<= x) xs)
    f x [] = QNil
    f x (y :: xs) with (y <= x)
      | True = ?qSortAccA
      | False = ?qSortAccB

{-
    f x [y] with (y <= x)
      | True = QCons QNil QNil
      | False = QNil
    f x (y :: z :: xs) with (y <= x)
      | True = ?rhs
      | False = ?rhs2
-}

qsortA : List Nat -> List Nat
qsortA xs = qsortA' xs (qsortAcc xs)

---

-- via Acc

flemma : (x : a) -> (p : a -> Bool) -> (xs : List a) -> (filter p xs `shorter` (x :: xs))
flemma x p [] = LES LEZ
flemma x p (y :: xs) with (p y)
  | True = LES $ flemma x p xs
  | False = leS $ flemma x p xs

qsortAcc' : (xs : List Nat) -> Acc Main.shorter xs -> QSortAcc xs
qsortAcc' [] acc = QNil
qsortAcc' (x :: xs) (MkAcc acc)
    = QCons
        (qsortAcc' _ (acc $ flemma x (<= x) xs))
        (qsortAcc' _ (acc $ flemma x (>  x) xs))

qsort2 : List Nat -> List Nat
qsort2 xs = qsortA' xs $ qsortAcc' xs (wfShorter xs)

---

data Split : List a -> Type where
  SNil : Split []
  SOne : (x : a) -> Split [x]
  SMore :
    (x : a) -> (xs : List a)
    -> (y : a) -> (ys : List a)
    -> Split (x :: xs ++ y :: ys)

shorterL : xs `shorter` (xs ++ y :: ys)
shorterL {xs = []} = LES LEZ
shorterL {xs = (x :: xs)} = LES shorterL

shorterR : ys `shorter` (x :: xs ++ ys)
shorterR {xs = []} = LES leRefl
shorterR {xs = x :: xs} = leS $ shorterR {x=x}

pushL : (x : a) -> Split xs -> Split (x :: xs)
pushL x  SNil = SOne x
pushL x (SOne y) = SMore x [] y []
pushL x (SMore y ys z zs) = SMore x (y :: ys) z zs

split : (xs : List a) -> Split xs
split [] = SNil
split [x] = SOne x
split (x :: y :: xs) = step (1 + length xs) x y xs
  where
    step : (counter : Nat) -> (x, y : a) -> (xs : List a) -> Split (x :: y :: xs)
    step  Z    x y xs = SMore x [] y xs
    step (S Z) x y xs = SMore x [] y xs
    step (S (S k)) x y [] = SMore x [] y []
    step (S (S k)) x y (z :: xs) = pushL x $ step k y z xs

merge : List Nat -> List Nat -> List Nat
merge (x :: xs) (y :: ys) with (x <= y)
  | True  = x :: merge xs (y :: ys)
  | False = y :: merge (x :: xs) ys
merge [] ys = ys
merge xs [] = xs

msort1' : (xs : List Nat) -> (Acc Main.shorter xs) -> List Nat
msort1' xs acc with (split xs)
  msort1' []  acc | SNil = []
  msort1' [x] acc | SOne x = [x]
  msort1' (y :: ys ++ z :: zs) (MkAcc acc) | SMore y ys z zs
    = merge
        (msort1' (y :: ys) (acc $ shorterL {xs = y::ys}))
        (msort1' (z :: zs) (acc $ shorterR))

msort1 : List Nat -> List Nat
msort1 xs = msort1' xs (wfShorter xs)

---------------------------

data MSAcc : Split xs -> Type where
  MSNil : MSAcc SNil
  MSOne : (x : a) -> MSAcc (SOne x)
  MSMore :
    MSAcc (split (x :: xs))
    -> MSAcc (split (y :: ys))
    -> MSAcc (SMore x xs y ys)

lemmaL : (x : a) -> (xs : List a) -> (y : a) -> (ys : List a) -> (x :: xs) `shorter` (x :: xs ++ y :: ys)
lemmaL x [] y ys = LES (LES LEZ)
lemmaL x (z :: xs) y ys = LES $ lemmaL x xs y ys

lemmaR : (x : a) -> (xs : List a) -> (y : a) -> (ys : List a) -> (y :: ys) `shorter` (x :: xs ++ y :: ys)
lemmaR x [] y ys = LES $ LES leRefl
lemmaR x (z :: xs) y ys = leS $ lemmaR x xs y ys

msAcc : (xs : List Nat) -> Acc Main.shorter xs -> MSAcc (split xs)
msAcc xs acc with (split xs)
  msAcc [] acc | SNil = MSNil
  msAcc [x] acc | SOne x = MSOne x
  msAcc (y :: ys ++ z :: zs) (MkAcc acc) | SMore y ys z zs
    = MSMore
      (msAcc (y :: ys) $ acc (lemmaL y ys z zs))
      (msAcc (z :: zs) $ acc (lemmaR y ys z zs))

msort2' : (xs : List Nat) -> MSAcc (split xs) -> List Nat
msort2' xs acc with (split xs)
  msort2' [] MSNil | SNil = []
  msort2' [x] (MSOne x) | SOne x = [x]
  msort2' (y :: ys ++ z :: zs) (MSMore accL accR) | SMore y ys z zs
    = merge
        (msort2' (y :: ys) accL)
        (msort2' (z :: zs) accR)

msort2 : List Nat -> List Nat
msort2 xs = msort2' xs $ msAcc xs (wfShorter xs)

-- views for convenience
-- views for termination

-- Acc is more general induction hypothesis than QSortAcc
-- more general => easier to work with (easier to prove from)
  -- probably a bit harder to prove BUT
  -- still obviously true
  -- and proving the inductive step may be easier (actually feasible at all)

-- end up with views

-----------------------------------------------

%default total

data SimpleSplit : List a -> Type where
  SS : (ls : List a) -> (rs : List a) -> SimpleSplit (ls ++ rs)

data ValidSplit : Nat -> List a -> Type where
  VSZ : ValidSplit (S Z) (x :: y :: xs)
  VSS : ValidSplit n xs -> ValidSplit (S n) (x :: xs)

data SplitG : (List a -> Type) -> List a -> Type where
  SG : (rxs : srg xs) -> (rys : srg ys) -> SplitG srg (xs ++ ys)

data SplitRecG : List a -> Type where
  SRG : ((n : Nat) -> ValidSplit n xs -> SplitG SplitRecG xs) -> SplitRecG xs

splitAt : (n : Nat) -> (xs : List a) -> SimpleSplit xs
splitAt n [] = SS [] []
splitAt Z xs = SS [] xs
splitAt (S k) (x :: xs) with (splitAt k xs)
  splitAt (S k) (x :: ys ++ zs) | SS ys zs = SS (x :: ys) zs

splitRecG : (xs : List a) -> SplitRecG xs
splitRecG xs = SRG (splitG xs (wfSmaller xs))
  where
    splitG : (xs : List a) -> SizeAcc xs -> (n : Nat) -> ValidSplit n xs -> SplitG SplitRecG xs
    splitG xs acc Z vs impossible
    splitG [] acc (S k) vs impossible
    splitG [x] acc (S k) (VSS vs) impossible
    splitG (x :: y :: xs) (MkAcc acc) (S k) vs = f (x :: y :: xs) (splitAt (S k) (x :: y :: xs))
      where
        f : (xs : List a) -> SimpleSplit xs -> SplitG SplitRecG xs
        f (ys ++ zs) (SS ys zs) = SG (SRG $ splitG ys (acc $ ?rys)) (SRG $ splitG zs (acc ?rzs))
