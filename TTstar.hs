module TTstar where

data Nat = Z | S Nat deriving (Eq, Ord, Show)
type Name = String
data Relevance = I | R deriving (Eq, Ord, Show)
data Binder = Lam | Pi deriving (Eq, Ord, Show)
data Constant = Int Int | TInt | TType deriving (Eq, Ord, Show)
data Op = Plus deriving (Eq, Ord, Show)

data TT' r
    = V Name
    | Bind Binder r Name (TT' r) (TT' r)
    | App r (TT' r) (TT' r)
    | Prim Op
    | Case (TT' r) (TT' r) [Alt r]
    | C Constant
    deriving (Eq, Ord, Show)

data Alt r
    = ConCase Name r [Name] (TT' r)  -- relevance of tag + relevance of args
    | ConstCase Constant (TT' r)
    | DefaultCase (TT' r)
    deriving (Eq, Ord, Show)

data Def tm
    = Fun
        { dName :: Name
        , dType :: tm
        , dBody :: tm
        }
    | Con
        { dName :: Name
        , dType :: tm
        }
  deriving (Eq, Ord, Show)

type Program tm = [Def tm]

type TT = TT' (Maybe Relevance)
type TTstar = TT' Relevance

primType :: (Relevance -> r) -> Op -> TT' r
primType f Plus = Bind Pi (f R) "x" (C TInt) (Bind Pi (f R) "y" (C TInt) (C TInt))

constType :: Constant -> TT' r
constType (Int _) = C TInt
constType  TInt   = C TType
constType  TType  = C TType  -- woooo :)
