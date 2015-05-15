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
    | Case (TT' r) (TT' r) [Alt r]  -- scrutinee, scrutinee type, alts
    | C Constant
    deriving (Eq, Ord, Show)

data Alt r
    = ConCase Name r [Name] (TT' r)  -- relevance of tag + relevance of args
    | ConstCase Constant (TT' r)
    | DefaultCase (TT' r)
    deriving (Eq, Ord, Show)

data DefType r = Ctor | Fun (TT' r) deriving (Eq, Ord, Show)
data Def r = Def r Name (TT' r) (DefType r) deriving (Eq, Ord, Show)

newtype Program r = Prog [Def r]

type TT = TT' (Maybe Relevance)
type TTstar = TT' Relevance

primType :: (Relevance -> r) -> Op -> TT' r
primType f Plus = Bind Pi (f R) "x" (C TInt) (Bind Pi (f R) "y" (C TInt) (C TInt))

constType :: Constant -> TT' r
constType (Int _) = C TInt
constType  TInt   = C TType
constType  TType  = C TType  -- woooo :)

instance Functor TT' where
    fmap f (V n) = V n
    fmap f (Bind b r n ty tm) = Bind b (f r) n (fmap f ty) (fmap f tm)
    fmap f (App r fun arg) = App (f r) (fmap f fun) (fmap f arg)
    fmap f (Prim op) = Prim op
    fmap f (Case s sty alts) = Case (fmap f s) (fmap f sty) (map (fmap f) alts)
    fmap f (C c) = C c

instance Functor Alt where
    fmap f (ConCase cn r ns tm) = ConCase cn (f r) ns (fmap f tm)
    fmap f (ConstCase c tm) = ConstCase c (fmap f tm)
    fmap f (DefaultCase tm) = DefaultCase (fmap f tm)

instance Functor DefType where
    fmap f Ctor = Ctor
    fmap f (Fun tm) = Fun (fmap f tm)

instance Functor Def where
    fmap f (Def r n ty dt) = Def (f r) n (fmap f ty) (fmap f dt)

instance Functor Program where
    fmap f (Prog defs) = Prog (map (fmap f) defs)

instance Show r => Show (Program r) where
    show (Prog defs) = unlines $ map fmtDef defs
      where
        fmtDef (Def r n ty dt) = unlines
            [ fmtR r ++ " " ++ n ++ " : " ++ show ty
            , n ++ " = " ++ fmtDT dt
            ]

        fmtDT Ctor = "(constructor)"
        fmtDT (Fun tm) = show tm

        fmtR r = "[" ++ show r ++ "]"
