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
    | Prim Op [TT' r]
    | C Constant
    deriving (Eq, Ord, Show)

data Def tm = Fun
    { dName :: Name
    , dType :: tm
    , dBody :: tm
    }
    deriving (Eq, Ord, Show)

type Program tm = [Def tm]

type TT = TT' (Maybe Relevance)
type TTstar = TT' Relevance
