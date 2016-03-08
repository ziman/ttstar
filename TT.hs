{-# LANGUAGE FlexibleInstances #-}
module TT where

import Control.Applicative
import qualified Data.Map as M

data Name = UN String | IN String [Relevance] deriving (Eq, Ord)
data Relevance = E | R deriving (Eq, Ord, Show)
data Binder = Lam | Pi | Pat deriving (Eq, Ord, Show)

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
    | Bind Binder Name r (TT r) (TT r)
        -- ^ binder, nrty, reverse dep, body
    | App r (TT r) (TT r)
    | Let (Def r VoidConstrs) (TT r)
    | Case (TT r) (Maybe (TT r)) [Alt r]  -- scrutinee, return type, alts
    | Type
    | Erased
    deriving (Eq, Ord)

data Alt r
    = ConCase Name (TT r)  -- cn, relevance, arity, lambda-bound RHS
    | DefaultCase (TT r)
    deriving (Eq, Ord)

data Def r cs = Def Name r (TT r) (Maybe (TT r)) (Maybe (cs r)) deriving (Eq, Ord)
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
subst n tm t@(Bind b n' r ty tm')
    | n' == n   = t
    | otherwise = Bind b n' r (subst n tm ty) (subst n tm tm')
subst n tm (App r f x) = App r (subst n tm f) (subst n tm x)
subst n tm t@(Let (Def n' r ty mtm Nothing) tm')
    | n' == n = t
    | otherwise = Let (Def n' r (subst n tm ty) (subst n tm `fmap` mtm) Nothing) (subst n tm tm')
subst n tm (Case s ty alts) = Case (subst n tm s) (subst n tm <$> ty) (map (substAlt n tm) alts)
subst _ _  t@Erased = t
subst _ _  t@Type   = t

substAlt :: Name -> TT r -> Alt r -> Alt r
substAlt n tm (DefaultCase tm') = DefaultCase $ subst n tm tm'
substAlt n tm t@(ConCase cn tm') = ConCase cn $ subst n tm tm'

substCtx :: Name -> TT r -> Ctx r cs -> Ctx r cs
substCtx n tm = M.map $ substDef n tm

substDef :: Name -> TT r -> Def r cs -> Def r cs
-- XXX TODO HACK: what do we do with constraints here?
substDef n tm (Def dn r ty mtm mcs) = Def dn r (subst n tm ty) (subst n tm <$> mtm) mcs

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
