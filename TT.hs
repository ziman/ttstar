{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
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

-- The difference between Var and Postulate is that for Var, the value is unknown,
-- for postulate; the term itself is the value. A variable stands for something else,
-- a postulate stands for itself.
data Abstractness = Var | Postulate deriving (Eq, Ord, Show)
data Body r = Abstract Abstractness | Term (TT r) | Clauses [Clause r] deriving (Eq, Ord)
data Clause r = Clause { pvars :: [Def r VoidConstrs], lhs :: TT r,  rhs :: TT r } deriving (Eq, Ord)
data Def r cs = Def
    { defName :: Name
    , defR    :: r
    , defType :: TT r
    , defBody :: Body r
    , defConstraints :: Maybe (cs r)
    } deriving (Eq, Ord)
type Ctx r cs = M.Map Name (Def r cs)

newtype Program r cs = Prog { getDefs :: [Def r cs] } deriving (Eq, Ord)

csDef :: Def r cs -> Def r cs'
csDef (Def n r ty body Nothing) = Def n r ty body Nothing

unApply :: TT r -> (TT r, [(r, TT r)])
unApply tm = ua tm []
  where
    ua (App r f x) args = ua f ((r, x) : args)
    ua tm args = (tm, args)

mkApp :: TT r -> [(r, TT r)] -> TT r
mkApp f [] = f
mkApp f ((r, x) : xs) = mkApp (App r f x) xs

substMany :: Show (Body r) => Ctx r cs -> TT r -> TT r
substMany ctx tm = foldl phi tm $ M.toList ctx
  where
    phi t (n, Def _ _ _ (Term tm) Nothing) = subst n tm t
    phi t (n, Def _ _ _ body Nothing)
        = error $ "trying to substMany something strange:\n  " ++ show n ++ " ~> " ++ show body

rename :: Name -> Name -> TT r -> TT r
rename fromN toN = subst fromN (V toN)

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
substDef n tm (Def dn r ty body mcs)
    | n == dn
    = Def dn r (subst n tm ty) body mcs  -- don't subst in body because those vars refer to `dn`

    | otherwise
    = Def dn r (subst n tm ty) (substBody n tm body) mcs

substBody :: Name -> TT r -> Body r -> Body r
substBody n tm (Abstract a) = Abstract a
substBody n tm (Term t) = Term $ subst n tm t
substBody n tm (Clauses cls) = Clauses $ map (substClause n tm) cls

substClause :: Name -> TT r -> Clause r -> Clause r
substClause n tm (Clause pvs lhs rhs) = Clause (substDef n tm <$> pvs) (subst n tm lhs) (subst n tm rhs)

getFreshName :: Ctx r cs -> Name -> Name
getFreshName ctx (UN n) = head $ filter (`M.notMember` ctx) [UN (n ++ show i) | i <- [0..]]
getFreshName ctx n = error $ "trying to refresh non-UN: " ++ show n

rmForced :: TT r -> TT r
rmForced t@(V n) = t
rmForced (I n ty) = I n (rmForced ty)
rmForced (Bind b d tm) = Bind b (rmForcedDef d) (rmForced tm)
rmForced (App r f x) = App r (rmForced f) (rmForced x)
rmForced (Forced t) = t
rmForced Erased = Erased
rmForced Type = Type

rmForcedDef :: Def r cs -> Def r cs
rmForcedDef (Def n r ty (Clauses cls) mcs) = Def n r ty (Clauses $ map rmForcedClause cls) mcs
rmForcedDef (Def n r ty (Term tm) mcs) = Def n r ty (Term $ rmForced tm) mcs
rmForcedDef d@(Def n r ty (Abstract a) mcs) = d

rmForcedClause :: Clause r -> Clause r
rmForcedClause (Clause pvs lhs rhs) = Clause (map rmForcedDef pvs) (rmForced lhs) (rmForced rhs)
