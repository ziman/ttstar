data Nat
    = Z
    | S Nat
    deriving (Show)

data Name
    = UN String
    | MN Int String
    deriving (Show)

data Constant
    = I Int
    | B Bool
    | TInt
    | TBool
    | TType
    deriving (Show)

data Binder
    = Lam Type
    | Pi Type
    | Forall Type
    deriving (Show)

-- Erased (a -> b -> ...)    = strongest
-- a -> b -> ... -> Erased z = weakest

Pi a ta (Pi b tb ( tc ))

{-

data Value :
       (erased : Bool)
    -> (lazy : Bool)
    -> (unique : Bool)
    -> (universe : Nat)
    -> (ty : Type)
    -> Type
  where
    V  : (x : ty) -> Erased False False uq un ty
    VL : (x : ty) -> Erased False True  uq un ty  -- replaces Lazy+Delay
    VE : (x : ty) -> Erased True  l     uq un ty

proj : Erased e a -> a
proj (V  x) = x
proj (VE x) = x
proj (VL x) = x

The function
    f : a -> b -> c
is translated to:
    f : (a : Erased ?ea ?la ?uqa ?una x)
        -> (b : Erased ?eb ?lb ?uqb ?unb x)
        -> (c : Erased ?ec ?lc ?uqc ?unc x)

We don't want to leave ?ea, ?eb and ?ec in the resulting program
(also, they are not pi-quantified (erased/lazy/...)

All occurrences of "a" are replaced with (proj a).

-}

-- annotations on TT

data TT
    = P Name Type
    | Bind Name Binder TT
    | App TT TT
    | Const Constant
    deriving (Show)

data Ann = Ann
    { aLazy :: Bool
    , aUniv :: Nat
    , aUniq :: Bool
    , aType :: Type
    , aRelevant :: Bool
    }
    deriving (Show)

type Raw  = TT (Maybe Type)
type Term = TT Ann
type Type = TT ()
type Typed = TT Type

bndTy :: Binder -> Type
bndTy (Lam ty) = ty
bndTy (Pi ty) = ty
bndTy (Forall ty) = ty

tmAnn :: TT a -> a
tmAnn (P a n ty) = a
tmAnn (Bind a n b tm) = a
tmAnn (App a f x) = a
tmAnn (Const a c) = a

elabA :: Raw -> Typed
elabA (P    _ n ty) = P ty n ty
elabA (Bind _ n b tm) = Bind (
elabA tm = error $ "not implemented: " ++ show tm

testTmA :: Raw
testTmA = Bind Nothing (UN "x") (Pi (Const Nothing TInt)) (P Nothing (UN "x"))
