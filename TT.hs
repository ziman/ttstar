{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module TT where

import Control.Applicative
import qualified Data.Map as M

data Name = UN String | IN String [Relevance] | Blank deriving (Eq, Ord)
data Relevance = E | R deriving (Eq, Ord, Show)
data Binder = Lam | Pi | Let deriving (Eq, Ord, Show)

instance Show Name where
    show Blank  = "_"
    show (UN n) = n
    show (IN n rs) = n ++ "_" ++ concatMap show rs

newtype Void = Void Void deriving (Eq, Ord, Show)
type VoidConstrs = Const Void

voidElim :: Void -> a
voidElim (Void v) = voidElim v

data TT r
    = V Name
    | I Name (TT r)  -- instance of a global definition with a specific erasure type
    | Bind Binder (Def r VoidConstrs) (TT r)
    | App r (TT r) (TT r)
    deriving (Eq, Ord)

data Pat r
    = PV Name
    | PApp r (Pat r) (Pat r)
    | PForced (TT r)
    deriving (Eq, Ord)

-- The difference between Var and Postulate is that for Var, the value is unknown,
-- for postulate; the term itself is the value. A variable stands for something else,
-- a postulate stands for itself.
data Abstractness = Var | Postulate deriving (Eq, Ord, Show)
data Body r = Abstract Abstractness | Term (TT r) | Clauses [Clause r] deriving (Eq, Ord)
data Clause r = Clause { pvars :: [Def r VoidConstrs], lhs :: Pat r,  rhs :: TT r } deriving (Eq, Ord)
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

patUnApply :: Pat r -> (Pat r, [(r, Pat r)])
patUnApply tm = ua tm []
  where
    ua (PApp r f x) args = ua f ((r, x) : args)
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

patRename :: Name -> Name -> Pat r -> Pat r
patRename fromN toN = substPat fromN (V toN)

subst :: Name -> TT r -> TT r -> TT r
subst n tm t@(V n')
    | n' == n   = tm
    | otherwise = t

subst n tm t@(I n' ty) = I n' $ subst n tm ty

subst n tm (Bind b d@(Def n' r ty body Nothing) tm')
    | n == n'
    = Bind b d' tm'

    | n' `occursIn` tm
    = let d'' = d'{ defName = freshName, defBody = substBody n' (V freshName) (defBody d') }
        in Bind b d'' (subst n tm . subst n' (V freshName) $ tm')

    | otherwise
    = Bind b d' (subst n tm tm')
  where
    freshName = head . filter (not . (`occursIn` tm)) $ [UN (show n' ++ show i) | i <- [0..]]
    d' = substDef n tm d

subst n tm (App r f x) = App r (subst n tm f) (subst n tm x)

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
substClause n tm (Clause pvs lhs rhs) = Clause (substDef n tm <$> pvs) (substPat n tm lhs) (subst n tm rhs)

substPat :: Name -> TT r -> Pat r -> Pat r
substPat n tm pat@(PV n')
    | n /= n'     = pat
    | V n'' <- tm = PV n''
    | otherwise   = error  $ "cannot substitute arbitrary terms in patterns"
substPat n tm (PApp r f x) = PApp r (substPat n tm f) (substPat n tm x)
substPat n tm (PForced t) = PForced $ subst n tm t

getFreshName :: Ctx r cs -> Name -> Name
getFreshName ctx (UN n) = head $ filter (`M.notMember` ctx) [UN (n ++ show i) | i <- [0..]]
getFreshName ctx n = error $ "trying to refresh non-UN: " ++ show n

pat2tt :: Pat r -> TT r
pat2tt (PV n) = V n
pat2tt (PApp r f x) = App r (pat2tt f) (pat2tt x)
pat2tt (PForced tm) = tm

-- this is only for patterns
refersTo :: TT r -> Name -> Bool
refersTo (V n) n' = n == n'
refersTo (I n ty) n' = n == n'
refersTo (Bind b d tm) n' = error $ "binder in pattern: " ++ show b
refersTo (App r f x) n' = (f `refersTo` n') || (x `refersTo` n')

occursIn :: Name -> TT r -> Bool
n `occursIn` V n' = (n == n')
n `occursIn` I n' ty = (n == n') || (n `occursIn` ty)
n `occursIn` Bind b d tm = (n `occursInDef` d) || (n `occursIn` tm)
n `occursIn` App r f x = (n `occursIn` f) || (n `occursIn` x)

occursInDef :: Name -> Def r cs -> Bool
occursInDef n (Def n' r ty body cs)
    | n == n'
    = n `occursIn` ty

    | otherwise
    = (n `occursIn` ty) || (n `occursInBody` body)

occursInBody :: Name -> Body r -> Bool
occursInBody n (Abstract _) = False
occursInBody n (Term tm) = n `occursIn` tm
occursInBody n (Clauses cls) = any (n `occursInClause`) cls

occursInClause :: Name -> Clause r -> Bool
occursInClause n (Clause pvs lhs rhs)
    | n `elem` map defName pvs
    = False

    | otherwise
    = (n `occursInPat` lhs) || (n `occursIn` rhs)

occursInPat :: Name -> Pat r -> Bool
occursInPat n (PV n') = n == n'
occursInPat n (PApp r f x) = (n `occursInPat` f) || (n `occursInPat` x)
occursInPat n (PForced tm) = n `occursIn` tm

builtins :: r -> Ctx r cs
builtins r = M.fromList
    [ (UN "Type", Def (UN "Type") r (V $ UN "Type") (Abstract Postulate) Nothing)
    ]
