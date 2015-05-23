module TT where

import Data.List
import Data.Foldable
import Data.Monoid
import qualified Data.Map as M

type Name = String
data Relevance = I | R deriving (Eq, Ord, Show)
data Binder = Lam | Pi | Pat deriving (Eq, Ord, Show)

data TT r
    = V Name
    | Bind Binder Name r (TT r) (TT r)
    | App r r (TT r) (TT r)
    | Case (TT r) [Alt r]  -- scrutinee, scrutinee type, alts
    | Type
    | Erased
    deriving (Eq, Ord)

data Alt r
    = ConCase Name r (TT r)  -- cn, relevance, arity, lambda-bound RHS
    | DefaultCase (TT r)
    deriving (Eq, Ord)

data DefType r = Axiom | Fun (TT r) deriving (Eq, Ord)
data Def r = Def Name r (TT r) (DefType r) deriving (Eq, Ord)
type Ctx r cs = M.Map Name (r, TT r, Maybe (TT r), cs)

newtype Program r = Prog [Def r] deriving (Eq, Ord)

type MRel = Maybe Relevance

instance Functor TT where
    fmap _ (V n) = V n
    fmap f (Bind b n r ty tm) = Bind b n (f r) (fmap f ty) (fmap f tm)
    fmap f (App pi_r r fun arg) = App (f pi_r) (f r) (fmap f fun) (fmap f arg)
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
    fmap f (Def n r ty dt) = Def n (f r) (fmap f ty) (fmap f dt)

instance Functor Program where
    fmap f (Prog defs) = Prog (map (fmap f) defs)

instance Foldable TT where
    fold (V n) = mempty
    fold (Bind b n r ty tm) = r `mappend` fold ty `mappend` fold tm
    fold (App pi_r r f x) = pi_r `mappend` r `mappend` fold f `mappend` fold x
    fold (Case s alts) = fold s `mappend` mconcat (map fold alts)
    fold Erased = mempty
    fold Type = mempty

instance Foldable Alt where
    fold (ConCase cn r tm) = r `mappend` fold tm
    fold (DefaultCase tm) = fold tm

unApply :: TT r -> (TT r, [TT r])
unApply tm = ua tm []
  where
    ua (App _ _ f x) args = ua f (x : args)
    ua tm args = (tm, args)

subst :: Name -> TT r -> TT r -> TT r
subst n tm t@(V n')
    | n' == n   = tm
    | otherwise = t
subst n tm t@(Bind b n' r ty tm')
    | n' == n   = t
    | otherwise = Bind b n' r (subst n tm ty) (subst n tm tm')
subst n tm (App pi_r r f x) = App pi_r r (subst n tm f) (subst n tm x)
subst n tm (Case s alts) = Case (subst n tm s) (map (substAlt n tm) alts)
subst _ _  t@Erased = t
subst _ _  t@Type   = t

substAlt :: Name -> TT r -> Alt r -> Alt r
substAlt n tm (DefaultCase tm') = DefaultCase $ subst n tm tm'
substAlt n tm t@(ConCase cn r tm') = ConCase cn r $ subst n tm tm'

-- split a Pat-packed pattern into 1. pattern vars, 2. RHS
splitBinder :: Binder -> TT r -> ([(Name, r, TT r)], TT r)
splitBinder bnd (Bind b n r ty tm)
    | b == bnd
    = ((n, r, ty) : args, rhs)
  where
    (args, rhs) = splitBinder bnd tm
splitBinder bnd tm = ([], tm)

fromPat :: Binder -> TT r -> TT r
fromPat b (Bind Pat n r ty tm) = Bind b n r ty $ fromPat b tm
fromPat b tm = tm
