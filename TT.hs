{-# LANGUAGE FlexibleInstances #-}
module TT where

import Control.Applicative
import qualified Data.Map as M

data Name = UN String | IN String [Relevance] deriving (Eq, Ord)
data Relevance = E | R deriving (Eq, Ord, Show)
data Binder = Lam | Pi | Let deriving (Eq, Ord, Show)

instance Show Name where
    show (UN n) = n
    show (IN n rs) = n ++ "_" ++ concatMap show rs

newtype Void = Void Void deriving (Eq, Ord, Show)
type VoidConstrs = Const Void

voidElim :: Void -> a
voidElim (Void v) = voidElim v

data TT r
    = V Name
    | I Name (TT r)  -- instance of a global definition with a specific type
    | Bind Binder (Def r VoidConstrs) (TT r)
    | App r (TT r) (TT r)
    | Type
    | Erased
    | Forced (TT r)  -- forced pattern
    deriving (Eq, Ord)

data Clause r = Clause { pvars :: [Def r VoidConstrs], lhs :: TT r,  rhs :: TT r } deriving (Eq, Ord)
data Def r cs = Def Name r (TT r) [Clause r] (Maybe (cs r)) deriving (Eq, Ord)
type Ctx r cs = M.Map Name (Def r cs)

newtype Program r cs = Prog { getDefs :: [Def r cs] } deriving (Eq, Ord)

unApply :: TT r -> (TT r, [TT r])
unApply tm = ua tm []
  where
    ua (App _ f x) args = ua f (x : args)
    ua tm args = (tm, args)

subst :: Name -> TT r -> TT r -> TT r
subst n tm t@(V n')
    | n' == n   = tm
    | otherwise = t
subst n tm t@(I n' ty) = I n' $ subst n tm ty
subst n tm (Bind b d@(Def n' r ty body Nothing) tm')
    = Bind b
        (substDef n tm d)
        (if n == n'
            then tm'
            else subst n tm tm')
subst n tm (App r f x) = App r (subst n tm f) (subst n tm x)
subst n tm (Forced t) = Forced (subst n tm t)
subst _ _  t@Erased = t
subst _ _  t@Type   = t

substCtx :: Name -> TT r -> Ctx r cs -> Ctx r cs
substCtx n tm = M.map $ substDef n tm

substDef :: Name -> TT r -> Def r cs -> Def r cs
-- XXX TODO HACK: what do we do with constraints here?
substDef n tm (Def dn r ty cls mcs) = Def dn r (subst n tm ty) (substClause n tm <$> cls) mcs

substClause :: Name -> TT r -> Clause r -> Clause r
substClause n tm (Clause pvs lhs rhs) = Clause (substDef n tm <$> pvs) (subst n tm lhs) (subst n tm rhs)

{-
-- split a Pat-packed pattern into 1. pattern vars, 2. RHS
splitBinder :: Binder -> TT r -> ([Def r], TT r)
splitBinder bnd (Bind b d tm)
    | b == bnd = (d : args, rhs)
  where
    (args, rhs) = splitBinder bnd tm
splitBinder bnd tm = ([], tm)
-}
