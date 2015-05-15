module TTstar where

import Data.List

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
    | Case (TT' r) [Alt r]  -- scrutinee, scrutinee type, alts
    | C Constant
    deriving (Eq, Ord)

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
    fmap _ (V n) = V n
    fmap f (Bind b r n ty tm) = Bind b (f r) n (fmap f ty) (fmap f tm)
    fmap f (App r fun arg) = App (f r) (fmap f fun) (fmap f arg)
    fmap _ (Prim op) = Prim op
    fmap f (Case s alts) = Case (fmap f s) (map (fmap f) alts)
    fmap _ (C c) = C c

instance Functor Alt where
    fmap f (ConCase cn r ns tm) = ConCase cn (f r) ns (fmap f tm)
    fmap f (ConstCase c tm) = ConstCase c (fmap f tm)
    fmap f (DefaultCase tm) = DefaultCase (fmap f tm)

instance Functor DefType where
    fmap _ Ctor = Ctor
    fmap f (Fun tm) = Fun (fmap f tm)

instance Functor Def where
    fmap f (Def r n ty dt) = Def (f r) n (fmap f ty) (fmap f dt)

instance Functor Program where
    fmap f (Prog defs) = Prog (map (fmap f) defs)

class Show r => ShowR r where
    showR :: r -> String
    showX :: r -> String

instance ShowR Relevance where
    showR x = ":" ++ show x ++ ":"
    showX x = " -" ++ show x ++ "- "

instance ShowR () where
    showR _ = ":"
    showX _ = " "

instance ShowR r => Show (Program r) where
    show (Prog defs) = intercalate "\n" $ map fmtDef defs
      where
        fmtDef (Def r n ty dt) = intercalate "\n"
            [ n ++ " " ++ showR r ++ " " ++ show ty
            , n ++ " = " ++ fmtDT dt
            , ""
            ]

        fmtDT Ctor = "(constructor)"
        fmtDT (Fun tm) = show tm

instance ShowR r => Show (TT' r) where
    show (V n) = n
    show (Bind Pi r n ty tm) = "(" ++ n ++ showR r ++ show ty ++ ") -> " ++ show tm
    show (Bind Lam r n ty tm) = "\\" ++ n ++ showR r ++ show ty ++ ". " ++ show tm
    show (App r f x) = "(" ++ show f ++ showX r ++ show x ++ ")"
    show (Prim op) = show op
    show (Case s alts) = "case " ++ show s ++ " of " ++ show alts
    show (C c) = show c

subst :: Name -> TT' r -> TT' r -> TT' r
subst n tm t@(V n')
    | n' == n   = tm
    | otherwise = t
subst n tm t@(Bind b r n' ty tm')
    | n' == n   = t
    | otherwise = Bind b r n' (subst n tm ty) (subst n tm tm')
subst n tm (App r f x) = App r (subst n tm f) (subst n tm x)
subst _ _  t@(Prim _op) = t
subst n tm (Case s alts) = Case (subst n tm s) (map (substAlt n tm) alts)
subst _ _  t@(C _c) = t

substAlt :: Name -> TT' r -> Alt r -> Alt r
substAlt n tm (DefaultCase tm') = DefaultCase $ subst n tm tm'
substAlt n tm (ConstCase c tm') = ConstCase c $ subst n tm tm'
substAlt n tm t@(ConCase cn r ns tm')
    | n `elem` ns = t
    | otherwise   = ConCase cn r ns $ subst n tm tm'
