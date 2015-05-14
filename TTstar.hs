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

type TT = TT' ()
type TTstar = TT' Relevance

infixr 3 ~>
(~>) :: TT -> TT -> TT
(~>) = Bind Pi () "_"

infixr 3 .->
(.->) :: String -> TT -> TT
n .-> tm = Bind Lam () n (C TInt) tm

infixr 4 !
(!) :: TT -> TT -> TT
(!) = App ()

testTerm :: TT
testTerm = "x" .-> V "x"

testProg :: [Def TT]
testProg =
    [ Fun
      { dName = "const_42"
      , dType = intFun
      , dBody = "x" .-> C (Int 42)
      }
    , Fun
      { dName = "id"
      , dType = intFun
      , dBody = "x" .-> V "x"
      }
    , Fun
      { dName = "f"
      , dType = intFun ~> C TInt ~> intFun ~> C TInt ~> C TInt
      , dBody = "g" .-> "x" .-> "h" .-> "y" .-> Prim Plus [V "g" ! V "x", V "h" ! V "y"]
      }
    ]
  where
    intFun = C TInt ~> C TInt
