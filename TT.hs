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

data CaseFun r = CaseFun [Def r VoidConstrs] (CaseTree r) deriving (Eq, Ord)

data CaseTree r
    = Leaf (TT r)
    | Case (TT r) [Alt r]
    deriving (Eq, Ord)

data AltLHS r
    = Ctor Name [Def r VoidConstrs] [(Name, TT r)]
    | Wildcard
    deriving (Eq, Ord)

data Alt r = Alt (AltLHS r) (CaseTree r) deriving (Eq, Ord)

-- The difference between Var and Postulate is that for Var, the value is unknown,
-- for postulate; the term itself is the value. A variable stands for something else,
-- a postulate stands for itself.
data Abstractness = Var | Postulate deriving (Eq, Ord, Show)
data Body r = Abstract Abstractness | Term (TT r) | Patterns (CaseFun r) deriving (Eq, Ord)
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

substLots :: (Name -> TT r -> a -> a) -> [(Name, TT r)] -> a -> a
substLots substF ss x = foldr (uncurry substF) x ss

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
substBody n tm (Patterns cf) = Patterns $ substCaseFun n tm cf

substCaseFun :: Name -> TT r -> CaseFun r -> CaseFun r
substCaseFun n tm cf@(CaseFun args ct)
    | n `elem` map defName args = cf
    | otherwise = CaseFun args $ substCaseTree n tm ct

substCaseTree :: Name -> TT r -> CaseTree r -> CaseTree r
substCaseTree n tm (Leaf t) = Leaf $ subst n tm t
substCaseTree n tm (Case s alts) = Case (subst n tm s) $ map (substAlt n tm) alts

-- equations are pattern-only so they are not touched by substitution
substAlt :: Name -> TT r -> Alt r -> Alt r
substAlt n tm (Alt Wildcard rhs) = Alt Wildcard $ substCaseTree n tm rhs
substAlt n tm alt@(Alt lhs@(Ctor cn args eqs) rhs)
    | n `elem` map defName args
    = alt  -- types of args refer to names bound here so there's nothing to do

{-
    -- if any bound name occurs in `tm`, we have to rename it
    | (`occursIn` tm) `any` (map defName args)
-}

    | otherwise
    = Alt lhs (substCaseTree n tm rhs)

getFreshName :: Ctx r cs -> Name -> Name
getFreshName ctx (UN n) = head $ filter (`M.notMember` ctx) [UN (n ++ show i) | i <- [0..]]
getFreshName ctx n = error $ "trying to refresh non-UN: " ++ show n

occursIn :: Name -> TT r -> Bool
n `occursIn` V n' = (n == n')
n `occursIn` I n' ty = (n == n') || (n `occursIn` ty)
n `occursIn` Bind b d tm
    | n == defName d = (n `occursInDef` d)
    | otherwise      = (n `occursInDef` d) || (n `occursIn` tm)
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
occursInBody n (Patterns cf) = n `occursInCaseFun` cf

occursInCaseFun :: Name -> CaseFun r -> Bool
occursInCaseFun n (CaseFun args ct)
    = (n `notElem` map defName args)
    && (n `occursInCaseTree` ct)

occursInCaseTree :: Name -> CaseTree r -> Bool
occursInCaseTree n (Leaf tm) = n `occursIn` tm
occursInCaseTree n (Case s alts) = (n `occursIn` s) || ((n `occursInAlt`) `any` alts)

occursInAlt :: Name -> Alt r -> Bool
occursInAlt n (Alt Wildcard rhs) = n `occursInCaseTree` rhs
occursInAlt n (Alt (Ctor cn args eqs) rhs)
    = (n `notElem` map defName args)
    && (n `occursInCaseTree` rhs)

builtins :: r -> Ctx r cs
builtins r = M.fromList
    [ (UN "Type", Def (UN "Type") r (V $ UN "Type") (Abstract Postulate) Nothing)
    ]
