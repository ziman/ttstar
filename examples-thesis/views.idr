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
    (acc : (y : a) -> (y `lessThan` x) -> Acc lessThan y)
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

wfLT : (x : Nat) -> Acc LT x
wfLT x = MkAcc (f x)
  where
    f : (x : Nat) -> (y : Nat) -> (y `LT` x) -> Acc LT y
    f (S x) y (LES yLEx) = MkAcc (\z, zLTy => f x z $ leTrans zLTy yLEx)
    -- LEZ cannot prove "strictly smaller than" because LT has (S _) on the LHS
    -- and LEZ has Z on the LHS

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
    f : (xs : List a) -> (ys : List a) -> (ys `Main.shorter` xs) -> Acc Main.shorter ys
    f (x :: xs) ys (LES ysLExs) = MkAcc (\zs, zsLTys => f xs zs $ leTrans zsLTys ysLExs)

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
wfSmaller x = MkAcc $ f (size x)
  where
    f : (sizeX : Nat) -> (y : a) -> (size y `LT` sizeX) -> SizeAcc y
    f (S n) y (LES yLEx)
      = MkAcc (\z, zLTy =>
          f n z (leTrans zLTy yLEx)
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

filterLen : {p : a -> Bool} -> {xs : List a} -> length (filter p xs) `LE` length xs
filterLen {xs = []} = LEZ
filterLen {p} {xs = x :: xs} with (p x)
  | True = LES $ filterLen
  | False = leS $ filterLen

qsort' : (xs : List Nat) -> (Acc Main.shorter xs) -> List Nat
qsort' [] acc = []
qsort' (x :: xs) (MkAcc acc) =
  qsort' (filter (<= x) xs) (acc _ $ LES filterLen)
  ++ [x]
  ++ qsort' (filter (> x) xs) (acc _ $ LES filterLen)

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

qsortAcc' : (xs : List Nat) -> Acc Main.shorter xs -> QSortAcc xs
qsortAcc' [] acc = QNil
qsortAcc' (x :: xs) (MkAcc acc)
    = QCons
        (qsortAcc' _ (acc _ $ LES filterLen))
        (qsortAcc' _ (acc _ $ LES filterLen))

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

pushL : (x : a) -> Split xs -> Split (x :: xs)
pushL x  SNil = SOne x
pushL x (SOne y) = SMore x [] y []
pushL x (SMore y ys z zs) = SMore x (y :: ys) z zs

{-
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
-}

halve : (xs : List a) -> Split xs
halve []  = SNil
halve [x] = SOne x
halve (x :: y :: xs) with (1 + length xs)
  halve (x :: y :: xs) |      Z  = SMore x [] y xs
  halve (x :: y :: xs) |    S Z  = SMore x [] y xs
  halve (x :: y :: []) | S (S k) = SMore x [] y []
  halve (x :: y :: z :: zs) | S (S k) = pushL x (halve (y :: z :: zs) | k)

shorterL : xs `shorter` (xs ++ y :: ys)
shorterL {xs = []} = LES LEZ
shorterL {xs = (x :: xs)} = LES shorterL

shorterR : ys `shorter` (x :: xs ++ ys)
shorterR {xs = []} = LES leRefl
shorterR {xs = x :: xs} = leS $ shorterR {x=x}

merge : List Nat -> List Nat -> List Nat
merge (x :: xs) (y :: ys) with (x <= y)
  | True  = x :: merge xs (y :: ys)
  | False = y :: merge (x :: xs) ys
merge [] ys = ys
merge xs [] = xs

msort1' : (xs : List Nat) -> (Acc Main.shorter xs) -> List Nat
msort1' xs acc with (halve xs)
  msort1' []  acc | SNil = []
  msort1' [x] acc | SOne x = [x]
  msort1' (y :: ys ++ z :: zs) (MkAcc acc) | SMore y ys z zs
    = merge
        (msort1' (y :: ys) (acc _ $ shorterL {xs = y::ys}))
        (msort1' (z :: zs) (acc _ $ shorterR {ys = z::zs}))

msort1 : List Nat -> List Nat
msort1 xs = msort1' xs (wfShorter xs)

---------------------------

mutual
  data MSAcc' : Split xs -> Type where
    MSNil : MSAcc' SNil
    MSOne : MSAcc' (SOne x)
    MSMore :
      MSAcc (x :: xs)
      -> MSAcc (y :: ys)
      -> MSAcc' (SMore x xs y ys)

  MSAcc : List a -> Type
  MSAcc xs = MSAcc' (halve xs)

msAcc : (xs : List Nat) -> MSAcc xs
msAcc xs with (wfShorter xs)
  msAcc xs | acc with (halve xs)
    msAcc []  | acc | SNil   = MSNil
    msAcc [x] | acc | SOne x = MSOne
    msAcc (y :: ys ++ z :: zs) | MkAcc acc | SMore y ys z zs
      = MSMore
        (msAcc _ | acc _ (shorterL {xs = y :: ys}))
        (msAcc _ | acc _ (shorterR {ys = z :: zs}))

msort2' : (xs : List Nat) -> MSAcc xs -> List Nat
msort2' xs acc with (halve xs)
  msort2' []  MSNil | SNil   = []
  msort2' [x] MSOne | SOne x = [x]
  msort2' (y :: ys ++ z :: zs) (MSMore accL accR) | SMore y ys z zs
    = merge
        (msort2' (y :: ys) accL)
        (msort2' (z :: zs) accR)

msort2 : List Nat -> List Nat
msort2 xs = msort2' xs (msAcc xs)

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

subst : (f : a -> Type) -> x = y -> f x -> f y
subst f Refl = \x => x

data SplitG : (List a -> Type) -> List a -> Type where
  SGNil : SplitG srg []
  SGOne : (x : a) -> SplitG srg [x]
  SGMore :
    (rxs : srg (x :: xs))
    -> (rys : srg (y :: ys))
    -> SplitG srg (x :: xs ++ y :: ys)

data SplitRecG : List a -> Type where
  SRG : ((n : Nat) -> SplitG SplitRecG xs) -> SplitRecG xs

pushSG : (x : a) -> SplitG (const ()) xs -> SplitG (const ()) (x :: xs)
pushSG x  SGNil = SGOne x
pushSG x (SGOne y) = SGMore {xs=[]} () ()
pushSG x (SGMore {x=y} {xs=ys} () ()) = SGMore {x=x} {xs=y::ys} () ()

splitAt : (n : Nat) -> (xs : List a) -> SplitG (const ()) xs
splitAt n [] = SGNil
splitAt n [x] = SGOne x
splitAt Z (x :: y :: xs) = SGMore {xs = []} () ()
splitAt (S k) (x :: y :: xs) = pushSG x $ splitAt k (y :: xs)

lemmaApp : (xs : List a) -> (ys : List a) -> length ys `LE` length (xs ++ ys)
lemmaApp []      ys = leRefl
lemmaApp (x::xs) ys = leS $ lemmaApp xs ys

splitG : (xs : List a) -> (n : Nat) -> SplitG SplitRecG xs
splitG xs n with (wfSmaller xs)
  splitG xs n | acc with (splitAt n xs)
    splitG []  n | acc | SGNil = SGNil
    splitG [x] n | acc | SGOne x = SGOne x
    splitG (y :: ys ++ z :: zs) n | MkAcc acc | SGMore () ()
        = SGMore
            (SRG $ \n' => splitG (y :: ys) n' | acc (y :: ys) (LES shorterL))
            (SRG $ \n' => splitG (z :: zs) n' | acc (z :: zs) (LES $ lemmaApp ys (z::zs)))

splitRecG : (xs : List a) -> SplitRecG xs
splitRecG xs = SRG $ splitG xs

{-
splitAt : (n : Nat) -> (xs : List a) -> SimpleSplit xs
splitAt n [] = SS [] []
splitAt Z xs = SS [] xs
splitAt (S k) (x :: xs) with (splitAt k xs)
  splitAt (S k) (x :: ys ++ zs) | SS ys zs = SS (x :: ys) zs

data SplitLemma : (xs : List a) -> SimpleSplit xs -> Type where
  SL : (l : length ys `LT` length (ys ++ zs))
    -> (r : length zs `LT` length (ys ++ zs))
    -> SplitLemma (ys ++ zs) (SS ys zs)

splitLemma : ValidSplit n xs -> SplitLemma xs (splitAt n xs)
splitLemma (VS x xs y ys) with (splitAt (length xs) (x :: xs ++ y :: ys))
  splitLemma (VS x xs y ys) | sa = ?rhs

splitLemma : (n : Nat) -> (xs : List a) -> ValidSplit n xs -> SplitLemma xs (splitAt n xs)
splitLemma (S Z) (x :: y :: ys) VSZ = SL (LES (LES LEZ)) (LES (LES leRefl))
splitLemma (S k) (x :: ys) (VSS vs) with (splitLemma k ys vs)
  splitLemma (S k) (x :: ys) (VSS vs) | sl with (splitAt k ys)
    splitLemma (S k) (x :: ls ++ rs) (VSS vs) | SL lsx rsx | (SS ls rs)
      = SL (LES lsx) (leS rsx)

mutual
  splitG : (xs : List a) -> SizeAcc xs -> (n : Nat) -> ValidSplit n xs -> SplitG SplitRecG xs
  splitG xs acc Z vs impossible
  splitG [] acc (S k) vs impossible
  splitG [x] acc (S k) (VSS vs) impossible
  splitG {a} (x :: y :: ws) (MkAcc acc) (S k) vs
      = splitG' ws (x :: y :: ws) acc (splitAt (S k) (x :: y :: ws)) (splitLemma (S k) (x :: y :: ws) vs)
  
  splitG' : (ws : List a) -> (qs : List a) -> ((ys : List a) -> Smaller ys qs -> SizeAcc ys)
      -> (sqs : SimpleSplit qs) -> SplitLemma qs sqs -> SplitG SplitRecG qs
  splitG' ws (ys ++ zs) acc (SS ys zs) (SL lx rx)
      = SG
          (SRG $ splitG ys (acc _ lx))
          (SRG $ splitG zs (acc _ rx))

splitRecG : (xs : List a) -> SplitRecG xs
splitRecG xs = SRG (splitG xs $ wfSmaller xs)
-}

{-
recG : (xs : List Nat) -> Nat
recG xs with (splitRecG xs)
  recG []  | SRG rec = 0
  recG [x] | SRG rec = x
  recG (x :: y :: xs) | SRG rec with (rec 1 VSZ)
    rec (x :: y :: xs ++ ys) | SRG rec | SG rxs rys = ?rhs_4
-}

{-
sub : Nat -> Nat -> Nat
sub (S m) (S n) = sub m n
sub _ n = n

mc91 : Nat -> Nat
mc91 n =
  case n > 100 of
    True  => sub 10 n
    False => mc91 (mc91 (11 + n))
-}

---------------------------------------------------------

{-
data ModView : Nat -> Nat -> Type where
  Base : ModView x y
  Step : ModView x y -> ModView x (x + y)

modView : (x', y : Nat) -> ModView (S x') y
modView  x'    Z = Base
modView  Z    (S y') = ?rhs_1  -- dividing by 1
modView (S k) (S y') = ?rhs_3
-}

{-
mod : (x : Nat) -> (y : Nat) -> Nat
mod x y acc with
-}

data SplitRec : List a -> Type where
  SRNil : SplitRec []
  SROne : (x : a) -> SplitRec [x]
  SRMore :
    (x : a) -> (xs : List a)    
    -> (y : a) -> (ys : List a)
    -> (sxs : SplitRec (x :: xs))
    -> (sys : SplitRec (y :: ys))
    -> SplitRec (x :: xs ++ y :: ys)

splitRec : (xs : List a) -> SplitRec xs
splitRec xs with (wfSmaller xs)
  splitRec xs | acc with (halve xs)
    splitRec []  | acc | SNil   = SRNil
    splitRec [x] | acc | SOne x = SROne x
    splitRec (y :: ys ++ z :: zs) | MkAcc acc | SMore y ys z zs
      = SRMore y ys z zs
          (splitRec _ | acc _ (shorterL {xs = y::ys}))
          (splitRec _ | acc _ (shorterR {x=z} {ys = z::zs}))

msortR : List Nat -> List Nat
msortR xs with (splitRec xs)
  msortR []  | SRNil   = []
  msortR [x] | SROne x = [x]
  msortR (y :: ys ++ z :: zs) | SRMore y ys z zs sys szs
    = merge
        (msortR (y :: ys) | sys)
        (msortR (z :: zs) | szs)
