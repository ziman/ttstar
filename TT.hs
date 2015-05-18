module TT where

import Data.List

type Name = String
data Relevance = I | R deriving (Eq, Ord, Show)
data Binder = Lam | Pi | Pat deriving (Eq, Ord, Show)

data TT r
    = V Name
    | Bind Binder r Name (TT r) (TT r)
    | App r (TT r) (TT r)
    | Case (TT r) [Alt r]  -- scrutinee, scrutinee type, alts
    | Type
    | Erased
    deriving (Eq, Ord)

data Alt r
    = ConCase Name r (TT r)  -- cn, relevance, arity, lambda-bound RHS
    | DefaultCase (TT r)
    deriving (Eq, Ord)

data DefType r = Axiom | Fun (TT r) deriving (Eq, Ord)
data Def r = Def r Name (TT r) (DefType r) deriving (Eq, Ord)

newtype Program r = Prog [Def r] deriving (Eq, Ord)

type MRel = Maybe Relevance

instance Functor TT where
    fmap _ (V n) = V n
    fmap f (Bind b r n ty tm) = Bind b (f r) n (fmap f ty) (fmap f tm)
    fmap f (App r fun arg) = App (f r) (fmap f fun) (fmap f arg)
    fmap f (Case s alts) = Case (fmap f s) (map (fmap f) alts)
    fmap _ Erased = Erased
    fmap _ Type = Type

instance Functor Alt where
    fmap f (ConCase cn r tm) = ConCase cn (f r) (fmap f tm)
    fmap f (DefaultCase tm) = DefaultCase (fmap f tm)

instance Functor DefType where
    fmap _  Axiom = Axiom
    fmap f (Fun tm) = Fun (fmap f tm)

instance Functor Def where
    fmap f (Def r n ty dt) = Def (f r) n (fmap f ty) (fmap f dt)

instance Functor Program where
    fmap f (Prog defs) = Prog (map (fmap f) defs)
